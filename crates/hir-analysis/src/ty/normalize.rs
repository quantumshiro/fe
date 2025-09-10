//! Type normalization module
//!
//! This module provides functionality to normalize types by resolving associated types
//! to concrete types when possible. This happens before type unification to ensure
//! that types are in their most resolved form.

use std::collections::hash_map::Entry;

use common::indexmap::IndexMap;
use hir::hir_def::{ImplTrait, scope_graph::ScopeId};
use rustc_hash::FxHashMap;

use super::{
    canonical::Canonical,
    fold::{TyFoldable, TyFolder},
    trait_resolution::{PredicateListId, constraint::collect_constraints},
    ty_def::{AssocTy, TyData, TyId, TyParam},
    ty_lower::lower_hir_ty,
    unify::UnificationTable,
};
use crate::{HirAnalysisDb, name_resolution::find_associated_type};

/// Normalizes a type by resolving all associated types to concrete types when possible.
///
/// This function takes a type and attempts to resolve any associated types within it
/// using the provided assumptions and scope context. It handles:
/// - Simple associated types (e.g., `T::Output`)
/// - Nested associated types (e.g., `T::Encoder::Output`)
/// - Associated types with generic parameters
pub fn normalize_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    ty: TyId<'db>,
    scope: ScopeId<'db>,
    assumptions: PredicateListId<'db>,
) -> TyId<'db> {
    let mut normalizer = TypeNormalizer {
        db,
        scope,
        assumptions,
        cache: FxHashMap::default(),
    };

    ty.fold_with(&mut normalizer)
}

struct TypeNormalizer<'db> {
    db: &'db dyn HirAnalysisDb,
    scope: ScopeId<'db>,
    assumptions: PredicateListId<'db>,
    // Projection cache: None = in progress (cycle guard), Some(ty) = normalized result
    cache: FxHashMap<AssocTy<'db>, Option<TyId<'db>>>,
}

impl<'db> TyFolder<'db> for TypeNormalizer<'db> {
    fn db(&self) -> &'db dyn HirAnalysisDb {
        self.db
    }

    fn fold_ty(&mut self, ty: TyId<'db>) -> TyId<'db> {
        match ty.data(self.db) {
            TyData::TyParam(p @ TyParam { owner, .. }) if p.is_trait_self() => {
                if let Some(impl_) = owner.resolve_to::<ImplTrait>(self.db)
                    && let Some(hir_ty) = impl_.ty(self.db).to_opt()
                {
                    let impl_assumptions =
                        collect_constraints(self.db, impl_.into()).instantiate_identity();
                    let lowered = lower_hir_ty(self.db, hir_ty, impl_.scope(), impl_assumptions);
                    // Continue folding the lowered type so it reaches normal form
                    return self.fold_ty(lowered);
                }
                ty
            }
            TyData::AssocTy(assoc_ty) => {
                match self.cache.entry(*assoc_ty) {
                    Entry::Occupied(entry) => match entry.get() {
                        Some(cached) => return *cached,
                        None => return ty, // cycle: leave unresolved
                    },
                    Entry::Vacant(entry) => {
                        entry.insert(None);
                    }
                }

                if let Some(replacement) = self.try_resolve_assoc_ty(ty, assoc_ty) {
                    let normalized = self.fold_ty(replacement);
                    self.cache.insert(*assoc_ty, Some(normalized));
                    return normalized;
                }

                // Not resolved; still fold internals (e.g., normalize self type)
                let folded = ty.super_fold_with(self);
                self.cache.insert(*assoc_ty, Some(folded));
                folded
            }
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'db> TypeNormalizer<'db> {
    fn try_resolve_assoc_ty(&mut self, ty: TyId<'db>, assoc: &AssocTy<'db>) -> Option<TyId<'db>> {
        // 1) Check if the trait instance itself carries an explicit binding
        if let Some(&bound_ty) = assoc.trait_.assoc_type_bindings(self.db).get(&assoc.name) {
            return Some(bound_ty);
        }

        // 2) Check assumptions for an equivalent trait instance that carries
        //    an explicit associated type binding (e.g., from where-clauses).
        for &pred in self.assumptions.list(self.db) {
            if pred.def(self.db) != assoc.trait_.def(self.db) {
                continue;
            }

            let mut table = UnificationTable::new(self.db);
            // Normalize self types before attempting unification to avoid
            // requiring a second outer pass for resolution.
            let lhs_self = self.fold_ty(assoc.trait_.self_ty(self.db));
            let rhs_self = self.fold_ty(pred.self_ty(self.db));
            if table.unify(lhs_self, rhs_self).is_ok()
                && let Some(&bound) = pred.assoc_type_bindings(self.db).get(&assoc.name)
            {
                return Some(bound.fold_with(&mut table));
            }
        }

        // 3) Fall back to the general associated type search used by path resolution,
        //    but restrict results to the same trait as `assoc` and deduplicate by
        //    the resulting type. If all viable candidates agree on a single type,
        //    normalize to that type.
        //    Search by the trait's self type: `SelfTy::assoc.name`.
        // Normalize the trait's self type before candidate search.
        let self_ty = self.fold_ty(assoc.trait_.self_ty(self.db));
        let mut raw_cands = find_associated_type(
            self.db,
            self.scope,
            Canonical::new(self.db, self_ty),
            assoc.name,
            self.assumptions,
        );

        // Keep only candidates from the same trait as `assoc`.
        raw_cands.retain(|(inst, _)| inst.def(self.db) == assoc.trait_.def(self.db));

        // Deduplicate by normalized result type (to handle cases where multiple
        // impls yield the same associated type, e.g., Output = Self for all impls).
        let mut dedup: IndexMap<TyId<'db>, ()> = IndexMap::new();
        for (_, t) in raw_cands.into_iter() {
            // Continue folding so nested associated types are also normalized
            let norm_t = self.fold_ty(t);
            dedup.entry(norm_t).or_insert(());
        }

        match dedup.len() {
            0 => None,
            1 => {
                let (unique, _) = dedup.first().unwrap();
                // Only replace if we're actually making progress
                if *unique != ty { Some(*unique) } else { None }
            }
            _ => None,
        }
    }
}
