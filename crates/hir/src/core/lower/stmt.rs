use parser::ast::{self, AttrListOwner, prelude::*};
use salsa::Accumulator as _;

use super::body::BodyCtxt;
use crate::{
    hir_def::{AttrListId, Cond, Expr, LoopUnrollAttrErrorKind, Pat, TypeId, stmt::*},
    span::HirOrigin,
};

#[salsa::accumulator]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LoopUnrollAttrError {
    pub kind: LoopUnrollAttrErrorKind,
    pub file: common::file::File,
    pub primary_range: parser::TextRange,
}

impl<'db> Stmt<'db> {
    pub(super) fn push_to_body(ctxt: &mut BodyCtxt<'_, 'db>, ast: ast::Stmt) -> StmtId {
        let (stmt, origin_kind) = match ast.kind() {
            ast::StmtKind::Let(let_) => {
                let pat = Pat::lower_ast_opt(ctxt, let_.pat());
                let ty = let_
                    .type_annotation()
                    .map(|ty| TypeId::lower_ast(ctxt.f_ctxt, ty));
                let init = let_.initializer().map(|init| Expr::lower_ast(ctxt, init));
                (Stmt::Let(pat, ty, init), HirOrigin::raw(&ast))
            }
            ast::StmtKind::For(for_) => {
                super::payable::report_payable_attr_on_unsupported_item(
                    ctxt.f_ctxt,
                    for_.attr_list(),
                    "for statement",
                );
                let bind = Pat::lower_ast_opt(ctxt, for_.pat());
                let iter = Expr::push_to_body_opt(ctxt, for_.iterable());
                let body = Expr::push_to_body_opt(
                    ctxt,
                    for_.body()
                        .and_then(|body| ast::Expr::cast(body.syntax().clone())),
                );
                let unroll_hint = lower_loop_unroll_hint(ctxt, for_.attr_list());

                (
                    Stmt::For(bind, iter, body, unroll_hint),
                    HirOrigin::raw(&ast),
                )
            }

            ast::StmtKind::While(while_) => {
                let cond = Cond::push_to_body_opt(ctxt, while_.cond());
                let body = Expr::push_to_body_opt(
                    ctxt,
                    while_
                        .body()
                        .and_then(|body| ast::Expr::cast(body.syntax().clone())),
                );

                (Stmt::While(cond, body), HirOrigin::raw(&ast))
            }

            ast::StmtKind::Continue(_) => (Stmt::Continue, HirOrigin::raw(&ast)),

            ast::StmtKind::Break(_) => (Stmt::Break, HirOrigin::raw(&ast)),

            ast::StmtKind::Return(ret) => {
                let expr = ret
                    .has_value()
                    .then(|| Expr::push_to_body_opt(ctxt, ret.expr()));
                (Stmt::Return(expr), HirOrigin::raw(&ast))
            }

            ast::StmtKind::Expr(expr) => {
                let expr = Expr::push_to_body_opt(ctxt, expr.expr());
                (Stmt::Expr(expr), HirOrigin::raw(&ast))
            }
        };

        ctxt.push_stmt(stmt, origin_kind)
    }
}

fn lower_loop_unroll_hint<'db>(
    ctxt: &mut BodyCtxt<'_, 'db>,
    attrs: Option<ast::AttrList>,
) -> Option<bool> {
    let lowered_attrs = AttrListId::lower_ast_opt(ctxt.f_ctxt, attrs.clone());
    let db = ctxt.f_ctxt.db();

    match lowered_attrs.parse_loop_unroll_attr(db) {
        Ok(hint) => hint,
        Err(err) => {
            let ranges = attrs
                .into_iter()
                .flatten()
                .filter_map(|attr| {
                    let ast::AttrKind::Normal(normal_attr) = attr.kind() else {
                        return None;
                    };
                    normal_attr
                        .is_named("unroll")
                        .then_some(attr.syntax().text_range())
                })
                .collect::<Vec<_>>();

            if let Some(primary_range) = ranges.get(err.attr_index) {
                LoopUnrollAttrError {
                    kind: err.kind,
                    file: ctxt.f_ctxt.top_mod().file(db),
                    primary_range: *primary_range,
                }
                .accumulate(db);
            }

            None
        }
    }
}
