use hir::{
    hir_def::{PathId, TypeId, scope_graph::ScopeId},
    span::{path::LazyPathSpan, types::LazyTySpan},
    visitor::{Visitor, VisitorCtxt, prelude::DynLazySpan, walk_path, walk_type},
};

use crate::{
    HirAnalysisDb,
    name_resolution::{
        ExpectedPathKind, PathRes, diagnostics::PathResDiag, resolve_path_with_observer,
    },
    ty::visitor::TyVisitor,
};

use super::{
    diagnostics::{TyDiagCollection, TyLowerDiag},
    trait_resolution::PredicateListId,
    ty_def::{InvalidCause, TyData, TyId},
    ty_lower::lower_hir_ty,
};

pub fn collect_ty_lower_errors<'db>(
    db: &'db dyn HirAnalysisDb,
    scope: ScopeId<'db>,
    hir_ty: TypeId<'db>,
    span: LazyTySpan<'db>,
    assumptions: PredicateListId<'db>,
) -> Vec<TyDiagCollection<'db>> {
    let mut vis = HirTyErrVisitor {
        db,
        assumptions,
        diags: Vec::new(),
    };
    let mut ctxt = VisitorCtxt::new(db, scope, span);
    vis.visit_ty(&mut ctxt, hir_ty);
    vis.diags
}

struct HirTyErrVisitor<'db> {
    db: &'db dyn HirAnalysisDb,
    diags: Vec<TyDiagCollection<'db>>,
    assumptions: PredicateListId<'db>,
}

impl<'db> HirTyErrVisitor<'db> {
    fn push_opt_diag(&mut self, diag: Option<TyDiagCollection<'db>>) {
        if let Some(diag) = diag {
            self.diags.push(diag)
        }
    }
}

impl<'db> Visitor<'db> for HirTyErrVisitor<'db> {
    fn visit_ty(&mut self, ctxt: &mut VisitorCtxt<'db, LazyTySpan<'db>>, hir_ty: TypeId<'db>) {
        let ty = lower_hir_ty(self.db, hir_ty, ctxt.scope(), self.assumptions);

        // This will report errors with nested types that are fundamental to the nested type,
        // but will not catch cases where the nested type is fine on its own, but incompatible
        // with the current type we're visiting. If !did_find_child_err, we use a TyVisitor to
        // report a diag about a nested invalid type; the downside of this is that the diag's
        // span will be too wide (it'll be the span of the current type, not the nested type).
        let before = self.diags.len();
        walk_type(self, ctxt, hir_ty);
        let did_fild_child_err = self.diags.len() > before;

        let span = ctxt.span().unwrap().into();
        match ty.data(self.db) {
            TyData::TyApp(base, _) if matches!(base.data(self.db), TyData::Invalid(..)) => {
                let TyData::Invalid(cause) = base.data(self.db) else {
                    unreachable!()
                };
                self.push_opt_diag(diag_from_invalid_cause(span, cause));
            }
            TyData::Invalid(cause) => self.push_opt_diag(diag_from_invalid_cause(span, cause)),
            _ => {
                // The span of a diag found here will cover the current type, not the nested
                // type. For example:
                //   Foo<true>
                //   ^^^^^^^^^ expected `u32`, but `bool` is given
                // (ideally this would only underline `true`).
                //
                // We could match other TyId structures manually to refine the spans
                // for common error cases.
                if !did_fild_child_err && ty.has_invalid(self.db) {
                    self.push_opt_diag(emit_invalid_ty_error(self.db, ty, span))
                }
            }
        }
    }

    fn visit_path(&mut self, ctxt: &mut VisitorCtxt<'db, LazyPathSpan<'db>>, path: PathId<'db>) {
        let scope = ctxt.scope();
        let path_span = ctxt.span().unwrap();

        let mut invisible = None;
        let mut check_visibility = |path: PathId<'db>, reso: &PathRes<'db>| {
            if invisible.is_some() {
                return;
            }
            if !reso.is_visible_from(self.db, scope) {
                invisible = Some((path, reso.name_span(self.db)));
            }
        };

        let res = match resolve_path_with_observer(
            self.db,
            path,
            scope,
            self.assumptions,
            false,
            &mut check_visibility,
        ) {
            Ok(res) => res,

            Err(err) => {
                let segment_idx = err.failed_at.segment_index(self.db);
                // Use the HIR path to check if the corresponding segment is a QualifiedType.
                let seg_hir = path.segment(self.db, segment_idx).unwrap_or(path);
                let segment = path_span.segment(segment_idx);
                let segment_span = match seg_hir.kind(self.db) {
                    hir::hir_def::PathKind::QualifiedType { .. } => {
                        segment.qualified_type().trait_qualifier().name()
                    }
                    _ => segment.ident(),
                };

                if let Some(diag) =
                    err.into_diag(self.db, path, segment_span.into(), ExpectedPathKind::Type)
                {
                    self.diags.push(diag.into());
                }
                return;
            }
        };

        if !matches!(res, PathRes::Ty(_) | PathRes::TyAlias(..)) {
            let ident = path.ident(self.db).to_opt().unwrap();
            let span = path_span.clone().segment(path.segment_index(self.db));
            self.diags
                .push(PathResDiag::ExpectedType(span.into(), ident, res.kind_name()).into());
        }
        if let Some((path, deriv_span)) = invisible {
            let span = path_span.segment(path.segment_index(self.db)).ident();
            let ident = path.ident(self.db);
            let diag = PathResDiag::Invisible(span.into(), *ident.unwrap(), deriv_span);
            self.diags.push(diag.into());
        }

        walk_path(self, ctxt, path);
    }
}

pub fn emit_invalid_ty_error<'db>(
    db: &'db dyn HirAnalysisDb,
    ty: TyId<'db>,
    span: DynLazySpan<'db>,
) -> Option<TyDiagCollection<'db>> {
    struct EmitDiagVisitor<'db> {
        db: &'db dyn HirAnalysisDb,
        diag: Option<TyDiagCollection<'db>>,
        span: DynLazySpan<'db>,
    }
    impl<'db> TyVisitor<'db> for EmitDiagVisitor<'db> {
        fn db(&self) -> &'db dyn HirAnalysisDb {
            self.db
        }
        fn visit_invalid(&mut self, cause: &InvalidCause<'db>) {
            if let Some(diag) = diag_from_invalid_cause(self.span.clone(), cause) {
                self.diag.get_or_insert(diag);
            }
        }
    }

    if !ty.has_invalid(db) {
        return None;
    }

    let mut visitor = EmitDiagVisitor {
        db,
        diag: None,
        span,
    };

    visitor.visit_ty(ty);
    visitor.diag
}

fn diag_from_invalid_cause<'db>(
    span: DynLazySpan<'db>,
    cause: &InvalidCause<'db>,
) -> Option<TyDiagCollection<'db>> {
    Some(match cause.clone() {
        InvalidCause::NotFullyApplied => TyLowerDiag::ExpectedStarKind(span).into(),

        InvalidCause::KindMismatch { expected, given } => TyLowerDiag::InvalidTypeArgKind {
            span,
            expected,
            given,
        }
        .into(),

        InvalidCause::TooManyGenericArgs { expected, given } => TyLowerDiag::TooManyGenericArgs {
            span,
            expected,
            given,
        }
        .into(),

        InvalidCause::InvalidConstParamTy => TyLowerDiag::InvalidConstParamTy(span).into(),

        InvalidCause::RecursiveConstParamTy => TyLowerDiag::RecursiveConstParamTy(span).into(),

        InvalidCause::ConstTyMismatch { expected, given } => TyLowerDiag::ConstTyMismatch {
            span,
            expected,
            given,
        }
        .into(),

        InvalidCause::ConstTyExpected { expected } => {
            TyLowerDiag::ConstTyExpected { span, expected }.into()
        }

        InvalidCause::NormalTypeExpected { given } => {
            TyLowerDiag::NormalTypeExpected { span, given }.into()
        }

        InvalidCause::UnboundTypeAliasParam {
            alias,
            n_given_args,
        } => TyLowerDiag::UnboundTypeAliasParam {
            span,
            alias,
            n_given_args,
        }
        .into(),

        InvalidCause::AliasCycle(cycle) => TyLowerDiag::TypeAliasCycle {
            cycle: cycle.to_vec(),
        }
        .into(),

        InvalidCause::InvalidConstTyExpr { body } => {
            TyLowerDiag::InvalidConstTyExpr(body.span().into()).into()
        }

        // These errors should be caught and reported elsewhere
        InvalidCause::PathResolutionFailed { .. }
        | InvalidCause::ParseError
        | InvalidCause::Other => return None,
    })
}
