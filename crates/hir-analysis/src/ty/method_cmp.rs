use thin_vec::ThinVec;

use super::{
    canonical::Canonical,
    diagnostics::{ImplDiag, TyDiagCollection},
    fold::{AssocTySubst, TyFoldable},
    func_def::FuncDef,
    normalize::normalize_ty,
    trait_def::{TraitInstId, TraitMethod},
    trait_resolution::{
        GoalSatisfiability, constraint::collect_func_def_constraints, is_goal_satisfiable,
    },
    ty_def::TyId,
};
use crate::HirAnalysisDb;

/// Compares the implementation method with the trait method to ensure they
/// match.
///
/// This function performs the following checks:
///
/// 1. Number of generic parameters.
/// 2. Kinds of generic parameters.
/// 3. Arity (number of arguments).
/// 4. Argument labels.
/// 5. Argument types and return type.
/// 6. Method constraints.
///
/// If any of these checks fail, the function will record the appropriate
/// diagnostics.
///
/// # Arguments
///
/// * `db` - Reference to the database implementing the `HirAnalysisDb` trait.
/// * `impl_m` - The implementation method to compare.
/// * `trait_m` - The trait method to compare against.
/// * `trait_inst` - The instance of the trait being checked.
/// * `implementor` - The implementor that contains associated type bindings.
/// * `sink` - A mutable reference to a vector where diagnostic messages will be
///   collected.
pub(super) fn compare_impl_method<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: TraitMethod<'db>,
    trait_inst: TraitInstId<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) {
    if !compare_generic_param_num(db, impl_m, trait_m.0, sink) {
        return;
    }

    if !compare_generic_param_kind(db, impl_m, trait_m.0, sink) {
        return;
    }

    if !compare_arity(db, impl_m, trait_m.0, sink) {
        return;
    }

    // Compare the argument labels, argument types, and return type of the impl
    // method with the trait method.
    let mut err = !compare_arg_label(db, impl_m, trait_m.0, sink);

    let map_to_impl: Vec<_> = trait_inst
        .args(db)
        .iter()
        .chain(impl_m.explicit_params(db).iter())
        .copied()
        .collect();
    err |= !compare_ty(db, impl_m, trait_m.0, &map_to_impl, trait_inst, sink);
    if err {
        return;
    }

    compare_constraints(db, impl_m, trait_m.0, &map_to_impl, sink);
}

/// Checks if the number of generic parameters of the implemented method is the
/// same as the number of generic parameters of the trait method.
/// Returns `false` if the comparison fails.
fn compare_generic_param_num<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let impl_params = impl_m.explicit_params(db);
    let trait_params = trait_m.explicit_params(db);

    if impl_params.len() == trait_params.len() {
        true
    } else {
        sink.push(ImplDiag::MethodTypeParamNumMismatch { trait_m, impl_m }.into());
        false
    }
}

/// Checks if the generic parameter kinds are the same.
/// Returns `false` if the comparison fails.
fn compare_generic_param_kind<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let mut err = false;
    for (idx, (&trait_m_param, &impl_m_param)) in trait_m
        .explicit_params(db)
        .iter()
        .zip(impl_m.explicit_params(db))
        .enumerate()
    {
        let trait_m_kind = trait_m_param.kind(db);
        let impl_m_kind = impl_m_param.kind(db);

        if !trait_m_kind.does_match(impl_m_kind) {
            sink.push(
                ImplDiag::MethodTypeParamKindMismatch {
                    trait_m,
                    impl_m,
                    param_idx: idx,
                }
                .into(),
            );
            err = true;
        }
    }

    !err
}

/// Checks if the arity of the implemented method is the same as the arity of
/// the trait method.
/// Returns `false` if the comparison fails.
fn compare_arity<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let impl_m_arity = impl_m.arg_tys(db).len();
    let trait_m_arity = trait_m.arg_tys(db).len();

    // Checks if the arity are the same.
    if impl_m_arity == trait_m_arity {
        true
    } else {
        sink.push(ImplDiag::MethodArgNumMismatch { impl_m, trait_m }.into());
        false
    }
}

/// Checks if the argument labels of the implemented method are the same as the
/// argument labels of the trait method.
/// Returns `false` if the comparison fails.
fn compare_arg_label<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let mut err = false;
    let hir_impl_m = impl_m.hir_func_def(db).unwrap();
    let hir_trait_m = trait_m.hir_func_def(db).unwrap();

    let (Some(impl_m_params), Some(trait_m_params)) = (
        hir_impl_m.params(db).to_opt(),
        hir_trait_m.params(db).to_opt(),
    ) else {
        return true;
    };

    for (idx, (expected_param, method_param)) in trait_m_params
        .data(db)
        .iter()
        .zip(impl_m_params.data(db))
        .enumerate()
    {
        let Some(expected_label) = expected_param
            .label
            .or_else(|| expected_param.name.to_opt())
        else {
            continue;
        };

        let Some(method_label) = method_param.label.or_else(|| method_param.name.to_opt()) else {
            continue;
        };

        if expected_label != method_label {
            sink.push(
                ImplDiag::MethodArgLabelMismatch {
                    trait_m,
                    impl_m,
                    param_idx: idx,
                }
                .into(),
            );
            err = true;
        }
    }

    !err
}

/// Checks if the argument types and return type of the implemented method are
/// the same as the argument types and return type of the trait method.
/// Returns `false` if the comparison fails.
fn compare_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    map_to_impl: &[TyId<'db>],
    trait_inst: TraitInstId<'db>,
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let mut err = false;
    let impl_m_arg_tys = impl_m.arg_tys(db);
    let trait_m_arg_tys = trait_m.arg_tys(db);

    let mut substituter = AssocTySubst::new(db, trait_inst);
    let assumptions =
        collect_func_def_constraints(db, impl_m.hir_def(db), true).instantiate_identity();

    for (idx, (&trait_m_ty, &impl_m_ty)) in trait_m_arg_tys.iter().zip(impl_m_arg_tys).enumerate() {
        // 1) Instantiate trait method's type params into the impl's generics
        let trait_m_ty = trait_m_ty.instantiate(db, map_to_impl);
        if trait_m_ty.has_invalid(db) {
            continue;
        }
        let impl_m_ty = impl_m_ty.instantiate_identity();

        // 2) Substitute associated types using the provided trait instance.
        let trait_m_ty_substituted = trait_m_ty.fold_with(&mut substituter);

        // 3) Normalize both types to resolve any further nested associated types.
        let trait_m_ty_normalized =
            normalize_ty(db, trait_m_ty_substituted, impl_m.scope(db), assumptions);
        let impl_m_ty_normalized = normalize_ty(db, impl_m_ty, impl_m.scope(db), assumptions);

        // 4) Compare for equality
        if !impl_m_ty.has_invalid(db) && trait_m_ty_normalized != impl_m_ty_normalized {
            sink.push(
                ImplDiag::MethodArgTyMismatch {
                    trait_m,
                    impl_m,
                    trait_m_ty: trait_m_ty_normalized,
                    impl_m_ty: impl_m_ty_normalized,
                    param_idx: idx,
                }
                .into(),
            );
            err = true;
        }
    }

    let impl_m_ret_ty = impl_m.ret_ty(db).instantiate_identity();
    let trait_m_ret_ty = trait_m.ret_ty(db).instantiate(db, map_to_impl);

    // Substitute and normalize the return type as well.
    let trait_m_ret_ty_substituted = trait_m_ret_ty.fold_with(&mut substituter);
    let trait_m_ret_ty_normalized = normalize_ty(
        db,
        trait_m_ret_ty_substituted,
        impl_m.scope(db),
        assumptions,
    );
    let impl_m_ret_ty_normalized = normalize_ty(db, impl_m_ret_ty, impl_m.scope(db), assumptions);

    if !impl_m_ret_ty.has_invalid(db)
        && !trait_m_ret_ty.has_invalid(db)
        && trait_m_ret_ty_normalized != impl_m_ret_ty_normalized
    {
        sink.push(
            ImplDiag::MethodRetTyMismatch {
                trait_m,
                impl_m,
                trait_ty: trait_m_ret_ty_normalized,
                impl_ty: impl_m_ret_ty_normalized,
            }
            .into(),
        );

        err = true;
    }

    !err
}

/// Checks if the method constraints are stricter than the trait constraints.
/// This check is performed by checking if the `impl_method` constraints are
/// satisfied under the assumptions that is obtained from the `expected_method`
/// constraints.
/// Returns `false` if the comparison fails.
fn compare_constraints<'db>(
    db: &'db dyn HirAnalysisDb,
    impl_m: FuncDef<'db>,
    trait_m: FuncDef<'db>,
    map_to_impl: &[TyId<'db>],
    sink: &mut Vec<TyDiagCollection<'db>>,
) -> bool {
    let impl_m_constraints =
        collect_func_def_constraints(db, impl_m.hir_def(db), false).instantiate_identity();
    let trait_m_constraints =
        collect_func_def_constraints(db, trait_m.hir_def(db), false).instantiate(db, map_to_impl);
    let mut unsatisfied_goals = ThinVec::new();
    for &goal in impl_m_constraints.list(db) {
        let canonical_goal = Canonical::new(db, goal);
        let ingot = trait_m.ingot(db);
        match is_goal_satisfiable(db, ingot, canonical_goal, trait_m_constraints) {
            GoalSatisfiability::Satisfied(_) | GoalSatisfiability::ContainsInvalid => {}
            GoalSatisfiability::NeedsConfirmation(_) => unreachable!(),
            GoalSatisfiability::UnSat(_) => {
                unsatisfied_goals.push(goal);
            }
        }
    }

    if unsatisfied_goals.is_empty() {
        true
    } else {
        sink.push(
            ImplDiag::MethodStricterBound {
                span: impl_m.name_span(db),
                stricter_bounds: unsatisfied_goals,
            }
            .into(),
        );
        false
    }
}
