use parser::ast;

use super::{define_lazy_span_node, types::LazyTySpan};
use crate::span::{LazySpanAtom, path::LazyPathSpan};

define_lazy_span_node!(
    LazyFuncParamListSpan,
    ast::FuncParamList,
    @idx {
        (param, LazyFuncParamSpan),
    }
);

define_lazy_span_node!(
    LazyGenericParamListSpan,
    ast::GenericParamList,
    @idx {
        (param, LazyGenericParamSpan),
    }
);

define_lazy_span_node!(
    LazyGenericArgListSpan,
    ast::GenericArgList,
    @idx {
        (arg, LazyGenericArgSpan),
    }

);
define_lazy_span_node!(
    LazyWhereClauseSpan,
    ast::WhereClause,
    @token {
        (where_token, where_kw),
    }
    @idx {
        (predicate, LazyWherePredicateSpan),
    }
);

define_lazy_span_node!(
    LazyFuncParamSpan,
    ast::FuncParam,
    @token {
       (mut_kw, mut_token),
    }
    @node {
       (label, label, LazySpanAtom),
       (name, name, LazySpanAtom),
       (ty, ty, LazyTySpan),
    }
);

impl<'db> LazyFuncParamSpan<'db> {
    pub fn fallback_self_ty(self) -> LazyTySpan<'db> {
        LazyTySpan(self.name().0)
    }
}

define_lazy_span_node!(LazyGenericParamSpan, ast::GenericParam);
impl<'db> LazyGenericParamSpan<'db> {
    pub fn into_type_param(self) -> LazyTypeGenericParamSpan<'db> {
        LazyTypeGenericParamSpan(self.0)
    }

    pub fn into_const_param(self) -> LazyConstGenericParamSpan<'db> {
        LazyConstGenericParamSpan(self.0)
    }
}

define_lazy_span_node!(
    LazyTypeGenericParamSpan,
    ast::TypeGenericParam,
    @token {
        (name, name),
    }
    @node {
        (bounds, bounds, LazyTypeBoundListSpan),
    }
);

define_lazy_span_node!(
    LazyConstGenericParamSpan,
    ast::ConstGenericParam,
    @token {
        (const_token, const_kw),
        (name, name),
    }
    @node {
        (ty, ty, LazyTySpan),
    }
);

define_lazy_span_node!(LazyGenericArgSpan);
impl<'db> LazyGenericArgSpan<'db> {
    pub fn into_type_arg(self) -> LazyTypeGenericArgSpan<'db> {
        LazyTypeGenericArgSpan(self.0)
    }

    pub fn into_assoc_type_arg(self) -> LazyAssocTypeGenericArgSpan<'db> {
        LazyAssocTypeGenericArgSpan(self.0)
    }
}

define_lazy_span_node!(
    LazyTypeGenericArgSpan,
    ast::TypeGenericArg,
    @node {
        (ty, ty, LazyTySpan),
    }
);

define_lazy_span_node!(
    LazyAssocTypeGenericArgSpan,
    ast::AssocTypeGenericArg,
    @token {
        (name, name),
    }
    @node {
        (ty, ty, LazyTySpan),
    }
);

define_lazy_span_node!(
    LazyWherePredicateSpan,
    ast::WherePredicate,
    @node {
        (ty, ty, LazyTySpan),
        (bounds, bounds, LazyTypeBoundListSpan),
    }
);

define_lazy_span_node! {
    LazyTypeBoundListSpan,
    ast::TypeBoundList,
    @idx {
        (bound, LazyTypeBoundSpan),
    }
}

define_lazy_span_node!(
    LazyTypeBoundSpan,
    ast::TypeBound,
    @node {
        (trait_bound, trait_bound, LazyTraitRefSpan),
        (kind_bound, kind_bound, LazyKindBoundSpan),
    }
);

define_lazy_span_node!(
    LazyTraitRefSpan,
    ast::TraitRef,
    @node {
        (path, path, LazyPathSpan),
    }
);

impl<'db> LazyTraitRefSpan<'db> {
    /// Returns the span atom for the trait name (last segment ident) in this trait ref.
    pub fn name(mut self) -> LazySpanAtom<'db> {
        use crate::span::transition::{LazyArg, LazyTransitionFn, ResolvedOrigin};
        use parser::ast::prelude::*;

        fn f(origin: ResolvedOrigin, _: LazyArg) -> ResolvedOrigin {
            origin.map(|node| {
                ast::TraitRef::cast(node)
                    .and_then(|tr| tr.path())
                    .and_then(|p| p.into_iter().last())
                    .and_then(|seg| seg.ident())
                    .map(|tok| tok.into())
            })
        }

        self.0.push(LazyTransitionFn {
            f,
            arg: LazyArg::None,
        });
        LazySpanAtom(self.0)
    }
}

define_lazy_span_node!(
    LazyKindBoundSpan,
    ast::KindBound,
    @node {
        (abs, abs, LazyKindBoundAbsSpan),
        (mono, mono, LazyKindBoundMonoSpan),
    }
);

define_lazy_span_node!(
    LazyKindBoundAbsSpan,
    ast::KindBoundAbs,
    @token {
        (arrow, arrow),
    }
    @node {
        (lhs, lhs, LazyKindBoundSpan),
        (rhs, rhs, LazyKindBoundSpan),
    }
);

define_lazy_span_node! {LazyKindBoundMonoSpan, ast::LazyKindBoundMono}
