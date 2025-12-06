//! Contract-specific type checking functions.
//!
//! This module contains functions for checking contract init bodies,
//! recv blocks, and recv arm bodies.
use rustc_hash::{FxHashMap, FxHashSet};

use super::{TypedBody, check_body_owner, owner::BodyOwner};

use crate::{
    HirDb,
    analysis::{
        HirAnalysisDb,
        name_resolution::{ExpectedPathKind, PathRes, diagnostics::PathResDiag, resolve_path},
        ty::{
            adt_def::AdtRef,
            canonical::Canonical,
            corelib::resolve_core_trait,
            diagnostics::{BodyDiag, FuncBodyDiag},
            trait_def::impls_for_ty,
            trait_resolution::PredicateListId,
            ty_def::TyId,
        },
    },
    hir_def::{Contract, IdentId, ItemKind, Mod, PathId, Struct, scope_graph::ScopeId},
    span::{DesugaredOrigin, DynLazySpan, HirOrigin, path::LazyPathSpan},
};

/// Returns true if a module was desugared from a `msg` block.
fn is_msg_mod<'db>(scope: ScopeId<'db>, db: &'db dyn HirDb) -> bool {
    if let ScopeId::Item(ItemKind::Mod(mod_)) = scope {
        matches!(
            mod_.origin(db),
            HirOrigin::Desugared(DesugaredOrigin::Msg(_))
        )
    } else {
        false
    }
}

/// Returns true if a struct implements the core MsgVariant trait.
fn implements_msg_variant<'db>(db: &'db dyn HirAnalysisDb, struct_: Struct<'db>) -> bool {
    let msg_variant_trait = resolve_core_trait(db, struct_.scope(), &["message", "MsgVariant"]);

    let adt_def = AdtRef::from(struct_).as_adt(db);
    let ty = TyId::adt(db, adt_def);
    let canonical_ty = Canonical::new(db, ty);
    let ingot = struct_.top_mod(db).ingot(db);

    impls_for_ty(db, ingot, canonical_ty)
        .iter()
        .any(|impl_| impl_.skip_binder().trait_def(db).eq(&msg_variant_trait))
}

/// Returns all variant structs in a msg module (structs that implement MsgVariant).
fn msg_variants<'db>(
    db: &'db dyn HirAnalysisDb,
    msg_mod: Mod<'db>,
) -> impl Iterator<Item = Struct<'db>> + 'db {
    msg_mod
        .children_non_nested(db)
        .filter_map(|item| match item {
            ItemKind::Struct(s) => Some(s),
            _ => None,
        })
        .filter(move |s| implements_msg_variant(db, *s))
}

/// Checks if a struct is a variant of a msg module (child of module AND implements MsgVariant).
fn is_variant_of_msg<'db>(
    db: &'db dyn HirAnalysisDb,
    msg_mod: Mod<'db>,
    struct_: Struct<'db>,
) -> bool {
    let struct_scope = struct_.scope();
    if let Some(parent_scope) = struct_scope.parent(db)
        && let ScopeId::Item(ItemKind::Mod(parent_mod)) = parent_scope
        && parent_mod == msg_mod
    {
        return implements_msg_variant(db, struct_);
    }
    false
}

/// Resolved msg variant in a recv arm.
#[derive(Debug, Clone, Copy)]
pub struct ResolvedRecvVariant<'db> {
    pub variant_struct: Struct<'db>,
    pub ty: TyId<'db>,
}

/// Resolves a variant path within a msg module.
/// Returns `Some` only if the resolved struct is a child of the msg module and implements MsgVariant.
pub fn resolve_variant_in_msg<'db>(
    db: &'db dyn HirAnalysisDb,
    msg_mod: Mod<'db>,
    variant_path: PathId<'db>,
    assumptions: PredicateListId<'db>,
) -> Option<ResolvedRecvVariant<'db>> {
    match resolve_path(db, variant_path, msg_mod.scope(), assumptions, false) {
        Ok(PathRes::Ty(ty)) => {
            if let Some(adt_def) = ty.adt_def(db)
                && let AdtRef::Struct(s) = adt_def.adt_ref(db)
                && is_variant_of_msg(db, msg_mod, s)
            {
                return Some(ResolvedRecvVariant {
                    variant_struct: s,
                    ty,
                });
            }
            None
        }
        _ => None,
    }
}

#[salsa::tracked(return_ref)]
pub fn check_contract_init_body<'db>(
    db: &'db dyn HirAnalysisDb,
    contract: Contract<'db>,
) -> (Vec<FuncBodyDiag<'db>>, TypedBody<'db>) {
    check_body_owner(db, BodyOwner::ContractInit(contract))
}

#[salsa::tracked(return_ref)]
pub fn check_contract_recv_block<'db>(
    db: &'db dyn HirAnalysisDb,
    contract: Contract<'db>,
    recv_idx: u32,
) -> Vec<FuncBodyDiag<'db>> {
    let mut diags = Vec::new();

    let Some(recv) = contract.recvs(db).data(db).get(recv_idx as usize) else {
        return diags;
    };

    let recv_span = contract.span().recv(recv_idx as usize);
    let path_span = recv_span.clone().path();

    let Some(msg_mod) = resolve_recv_msg_mod(
        db,
        contract,
        recv.msg_path,
        path_span.clone(),
        &mut diags,
        true,
    ) else {
        return diags;
    };

    let assumptions = PredicateListId::empty_list(db);
    let mut seen = FxHashMap::<Struct<'db>, DynLazySpan<'db>>::default();
    let mut covered = FxHashSet::<Struct<'db>>::default();

    // Get msg name for diagnostics
    let Some(msg_name) = msg_mod.name(db).to_opt() else {
        return diags;
    };

    for (arm_idx, arm) in recv.arms.data(db).iter().enumerate() {
        let pat_span: DynLazySpan<'db> = recv_span.clone().arms().arm(arm_idx).pat().into();

        let Some(path) = arm.variant_path(db) else {
            continue;
        };

        let Some(resolved) = resolve_variant_in_msg(db, msg_mod, path, assumptions) else {
            // Emit diagnostic when pattern doesn't resolve to a valid msg variant
            diags.push(
                BodyDiag::RecvArmNotMsgVariant {
                    primary: pat_span.clone(),
                    msg_name,
                }
                .into(),
            );
            continue;
        };

        let Some(ident) = resolved.variant_struct.name(db).to_opt() else {
            continue;
        };

        if let Some(first_span) = seen.get(&resolved.variant_struct) {
            diags.push(
                BodyDiag::RecvArmDuplicateVariant {
                    primary: pat_span.clone(),
                    first_use: first_span.clone(),
                    variant: ident,
                }
                .into(),
            );
        } else {
            seen.insert(resolved.variant_struct, pat_span.clone());
        }

        covered.insert(resolved.variant_struct);
    }

    // Check for missing variants
    let missing: Vec<_> = msg_variants(db, msg_mod)
        .filter_map(|variant| {
            if !covered.contains(&variant) {
                variant.name(db).to_opt()
            } else {
                None
            }
        })
        .collect();

    if !missing.is_empty() {
        diags.push(
            BodyDiag::RecvMissingMsgVariants {
                primary: recv_span.clone().path().into(),
                variants: missing,
            }
            .into(),
        );
    }

    diags
}

#[salsa::tracked(return_ref)]
pub fn check_contract_recv_blocks<'db>(
    db: &'db dyn HirAnalysisDb,
    contract: Contract<'db>,
) -> Vec<FuncBodyDiag<'db>> {
    let mut diags = Vec::new();
    let mut seen_msg_blocks = FxHashMap::<Mod<'db>, (DynLazySpan<'db>, IdentId<'db>)>::default();

    // Track selectors across ALL recv blocks: selector -> (span, variant_name, struct)
    // We store the struct to correctly identify duplicates - comparing by name alone fails
    // when different msg blocks have variants with the same name but different selectors.
    let mut seen_selectors =
        FxHashMap::<u32, (DynLazySpan<'db>, IdentId<'db>, Struct<'db>)>::default();

    for (idx, recv) in contract.recvs(db).data(db).iter().enumerate() {
        let recv_span = contract.span().recv(idx);
        let path_span = recv_span.clone().path();

        let Some(msg_mod) = resolve_recv_msg_mod(
            db,
            contract,
            recv.msg_path,
            path_span.clone(),
            &mut diags,
            false,
        ) else {
            continue;
        };

        let Some(msg_name) = msg_mod.name(db).to_opt() else {
            continue;
        };

        let path_span: DynLazySpan<'db> = path_span.into();
        if let Some((first_span, first_name)) = seen_msg_blocks.get(&msg_mod) {
            diags.push(
                BodyDiag::RecvDuplicateMsgBlock {
                    primary: path_span.clone(),
                    first_use: first_span.clone(),
                    msg_name: *first_name,
                }
                .into(),
            );
        } else {
            seen_msg_blocks.insert(msg_mod, (path_span.clone(), msg_name));
        }

        // Check for selector conflicts across all msg variants in this recv block
        for variant in msg_variants(db, msg_mod) {
            let Some(variant_name) = variant.name(db).to_opt() else {
                continue;
            };

            if let Some(selector) = get_variant_selector(db, variant) {
                // Use the struct's name span (points to variant name in msg block)
                let variant_span: DynLazySpan<'db> = variant.span().name().into();

                if let Some((first_span, first_variant, first_struct)) =
                    seen_selectors.get(&selector)
                {
                    // Don't report if it's the same variant (duplicate msg block already reported)
                    if *first_struct != variant {
                        diags.push(
                            BodyDiag::RecvDuplicateSelector {
                                primary: variant_span,
                                first_use: first_span.clone(),
                                selector,
                                first_variant: *first_variant,
                                second_variant: variant_name,
                            }
                            .into(),
                        );
                    }
                } else {
                    seen_selectors.insert(selector, (variant_span, variant_name, variant));
                }
            }
        }
    }

    diags
}

/// Gets the selector value from a msg variant struct by reading the SELECTOR const
/// from its MsgVariant impl. Used for cross-recv-block duplicate detection.
fn get_variant_selector<'db>(db: &'db dyn HirAnalysisDb, struct_: Struct<'db>) -> Option<u32> {
    use crate::hir_def::{Expr, LitKind};
    use num_traits::ToPrimitive;

    // Find the MsgVariant trait
    let msg_variant_trait = resolve_core_trait(db, struct_.scope(), &["message", "MsgVariant"]);

    // Get the impl for this struct
    let adt_def = AdtRef::from(struct_).as_adt(db);
    let ty = TyId::adt(db, adt_def);
    let canonical_ty = Canonical::new(db, ty);
    let ingot = struct_.top_mod(db).ingot(db);

    let impl_ = impls_for_ty(db, ingot, canonical_ty)
        .iter()
        .find(|impl_| impl_.skip_binder().trait_def(db).eq(&msg_variant_trait))?
        .skip_binder();

    // Get the SELECTOR const from the impl
    let selector_name = IdentId::new(db, "SELECTOR".to_string());
    let hir_impl = impl_.hir_impl_trait(db);

    let selector_const = hir_impl
        .hir_consts(db)
        .iter()
        .find(|c| c.name.to_opt() == Some(selector_name))?;

    // Extract the literal value from the const body
    let body = selector_const.value.to_opt()?;
    let root_expr = body.expr(db);
    let expr = body.exprs(db).get(root_expr)?.clone().to_opt()?;

    match expr {
        Expr::Lit(LitKind::Int(int_id)) => int_id.data(db).to_u32(),
        _ => None,
    }
}

#[salsa::tracked(return_ref)]
pub fn check_contract_recv_arm_body<'db>(
    db: &'db dyn HirAnalysisDb,
    contract: Contract<'db>,
    recv_idx: u32,
    arm_idx: u32,
) -> (Vec<FuncBodyDiag<'db>>, TypedBody<'db>) {
    let recv = contract.recvs(db).data(db).get(recv_idx as usize).unwrap();
    let arm = *recv.arms.data(db).get(arm_idx as usize).unwrap();

    check_body_owner(
        db,
        BodyOwner::ContractRecvArm {
            contract,
            recv_idx,
            arm_idx,
            msg_path: recv.msg_path,
            arm,
        },
    )
}

pub(super) fn resolve_recv_msg_mod<'db>(
    db: &'db dyn HirAnalysisDb,
    contract: Contract<'db>,
    msg_path: Option<PathId<'db>>,
    span: LazyPathSpan<'db>,
    diags: &mut Vec<FuncBodyDiag<'db>>,
    emit_diag: bool,
) -> Option<Mod<'db>> {
    let msg_path = msg_path?;
    let assumptions = PredicateListId::empty_list(db);

    match resolve_path(db, msg_path, contract.scope(), assumptions, false) {
        Ok(PathRes::Ty(ty) | PathRes::TyAlias(_, ty)) => {
            if emit_diag {
                diags.push(
                    BodyDiag::RecvExpectedMsgType {
                        primary: span.clone().into(),
                        given: ty,
                    }
                    .into(),
                );
            }
            None
        }
        Ok(PathRes::Mod(scope)) if is_msg_mod(scope, db) => {
            if let ScopeId::Item(ItemKind::Mod(mod_)) = scope {
                return Some(mod_);
            }
            unreachable!();
        }
        Ok(other) => {
            let ident = msg_path.ident(db).to_opt()?;
            if emit_diag {
                diags.push(PathResDiag::ExpectedType(span.into(), ident, other.kind_name()).into());
            }
            None
        }
        Err(err) => {
            if emit_diag
                && let Some(diag) = err.into_diag(db, msg_path, span, ExpectedPathKind::Type)
            {
                diags.push(diag.into());
            }
            None
        }
    }
}

/// Gets the Return type from a type's MsgVariant trait implementation.
/// Specifically looks for the MsgVariant trait and returns `None` if no impl is found.
pub(super) fn get_msg_variant_return_type<'db>(
    db: &'db dyn HirAnalysisDb,
    variant_ty: TyId<'db>,
    scope: ScopeId<'db>,
) -> Option<TyId<'db>> {
    let msg_variant_trait = resolve_core_trait(db, scope, &["message", "MsgVariant"]);

    let canonical_ty = Canonical::new(db, variant_ty);
    let ingot = scope.ingot(db);

    // Find the MsgVariant impl specifically
    let msg_variant_impl = impls_for_ty(db, ingot, canonical_ty)
        .iter()
        .find(|impl_| impl_.skip_binder().trait_def(db).eq(&msg_variant_trait))?;

    // Get the Return associated type from the impl
    let return_name = IdentId::new(db, "Return".to_string());
    msg_variant_impl.skip_binder().assoc_ty(db, return_name)
}
