use hir::hir_def::{InlineHint, params::FuncParamMode};
use hir::{
    analysis::{
        HirAnalysisDb,
        diagnostics::SpannedHirAnalysisDb,
        ty::{
            ty_check::{LocalBinding, ParamSite, PatBindingMode},
            ty_def::{InvalidCause, TyId},
        },
    },
    hir_def::expr::ExprId,
    semantic::{EffectBinding, EffectSource},
};

use crate::{
    core_lib::CoreLib,
    ir::{
        AddressSpaceKind, LocalId, MirBody, MirFunction, MirFunctionOrigin, MirInst,
        MirProjectionPath, Place, RuntimeAbi, RuntimeShape, Rvalue, SourceInfoId, SymbolSource,
        SyntheticId, SyntheticValue, Terminator, ValueId, ValueOrigin,
    },
    layout, repr,
};

use super::{
    MirBuilder, MirLowerResult,
    plan::{InitHandlerPlan, RecvHandlerPlan},
    symbols::SymbolMangler,
};

pub(super) fn emit_init_handler<'db>(
    db: &'db dyn SpannedHirAnalysisDb,
    contract: hir::hir_def::Contract<'db>,
    plan: &InitHandlerPlan<'db>,
    mangler: &SymbolMangler,
) -> MirLowerResult<Option<MirFunction<'db>>> {
    let symbol_name = mangler.symbol_for(plan.id);
    let mut builder =
        MirBuilder::new_for_body_owner(db, plan.body, &plan.typed_body, &[], TyId::unit(db))?;
    let mut zero_sized_param_bindings = Vec::new();
    let mut zero_sized_param_locals = Vec::new();

    for (idx, param) in plan.init.params(db).data(db).iter().enumerate() {
        let binding = builder
            .typed_body
            .param_binding(idx)
            .unwrap_or(LocalBinding::Param {
                site: ParamSite::ContractInit(contract),
                idx,
                mode: param.mode,
                ty: TyId::invalid(db, InvalidCause::Other),
                is_mut: param.is_mut,
            });
        let name = param
            .name()
            .map(|ident| ident.data(db).to_string())
            .unwrap_or_else(|| format!("arg{idx}"));
        let ty = match binding {
            LocalBinding::Param { ty, .. } => ty,
            _ => TyId::invalid(db, InvalidCause::Other),
        };
        let source_param_ty = plan.source_param_tys.get(idx).copied().unwrap_or(ty);
        if abi_payload_is_empty(db, source_param_ty) {
            zero_sized_param_bindings.push((binding, ty));
        } else {
            builder.seed_synthetic_param_local(name, ty, binding.is_mut(), Some(binding));
        }
    }

    seed_effect_param_locals(db, &mut builder, contract, &plan.effect_bindings);

    let entry = builder.builder.entry_block();
    builder.move_to_block(entry);
    for (binding, ty) in zero_sized_param_bindings {
        if let Some(local) = builder.local_for_binding(binding) {
            zero_sized_param_locals.push(local);
            let value = builder.builder.unit_value(ty);
            builder.assign(None, Some(local), Rvalue::Value(value));
        }
    }

    let mut function = finish_handler(
        db,
        builder,
        HandlerFinishSpec {
            body: plan.body,
            typed_body: plan.typed_body.clone(),
            id: plan.id,
            ret_ty: TyId::unit(db),
            return_behavior: ReturnBehavior::Unit,
            runtime_return_shape: RuntimeShape::Erased,
            returns_value: false,
            symbol_name,
        },
    )?;
    prune_redundant_fresh_storage_zero_stores(&mut function.body);
    function
        .body
        .param_locals
        .retain(|local| !zero_sized_param_locals.contains(local));
    function.runtime_abi = RuntimeAbi::source_shaped(
        function.body.param_locals.len(),
        vec![None; function.body.effect_param_locals.len()],
    );
    Ok(init_handler_has_observable_effects(&function.body).then_some(function))
}

pub(super) fn emit_recv_handler<'db>(
    db: &'db dyn SpannedHirAnalysisDb,
    contract: hir::hir_def::Contract<'db>,
    plan: &RecvHandlerPlan<'db>,
    mangler: &SymbolMangler,
) -> MirLowerResult<MirFunction<'db>> {
    let symbol_name = mangler.symbol_for(plan.id);
    let mut builder =
        MirBuilder::new_for_body_owner(db, plan.body, &plan.typed_body, &[], plan.ret_ty)?;
    let args_local = (!abi_payload_is_empty(db, plan.args_ty))
        .then(|| builder.seed_synthetic_param_local("args".to_string(), plan.args_ty, false, None));

    seed_effect_param_locals(db, &mut builder, contract, &plan.effect_bindings);

    let entry = builder.builder.entry_block();
    builder.move_to_block(entry);
    let args_value = if let Some(args_local) = args_local {
        builder.alloc_value(
            plan.args_ty,
            ValueOrigin::Local(args_local),
            builder.value_repr_for_ty(plan.args_ty, AddressSpaceKind::Memory),
        )
    } else {
        builder.builder.unit_value(plan.args_ty)
    };
    for binding in &plan.arg_bindings {
        let elem_value = builder.project_tuple_elem_value(
            args_value,
            plan.args_ty,
            binding.tuple_index as usize,
            binding.ty,
            PatBindingMode::ByValue,
        );
        builder.bind_pat_value(binding.pat, elem_value);
        if builder.current_block().is_none() {
            break;
        }
    }

    let returns_value = !builder.is_unit_ty(plan.ret_ty)
        && !plan.ret_ty.is_never(db)
        && !layout::is_zero_sized_ty(db, plan.ret_ty);
    finish_handler(
        db,
        builder,
        HandlerFinishSpec {
            body: plan.body,
            typed_body: plan.typed_body.clone(),
            id: plan.id,
            ret_ty: plan.ret_ty,
            return_behavior: ReturnBehavior::ExprValue {
                expr: plan.body.expr(db),
                returns_value,
            },
            runtime_return_shape: crate::repr::runtime_return_shape_seed_for_ty(
                db,
                &CoreLib::new(db, contract.scope()),
                plan.ret_ty,
            ),
            returns_value,
            symbol_name,
        },
    )
}

enum ReturnBehavior {
    Unit,
    ExprValue { expr: ExprId, returns_value: bool },
}

fn finish_handler<'db>(
    db: &'db dyn SpannedHirAnalysisDb,
    mut builder: MirBuilder<'db, '_>,
    spec: HandlerFinishSpec<'db>,
) -> MirLowerResult<MirFunction<'db>> {
    let root_expr = spec.body.expr(db);
    builder.lower_root(root_expr);
    builder.ensure_const_expr_values();
    if let Some(block) = builder.current_block() {
        let value = match spec.return_behavior {
            ReturnBehavior::Unit => None,
            ReturnBehavior::ExprValue {
                expr,
                returns_value,
            } => returns_value.then(|| builder.ensure_value(expr)),
        };
        builder.set_terminator(
            block,
            Terminator::Return {
                source: SourceInfoId::SYNTHETIC,
                value,
            },
        );
    }

    let deferred_error = builder.deferred_error.take();
    let mir_body = builder.finish();
    if let Some(err) = deferred_error {
        return Err(err);
    }
    super::super::validate_lowered_mir_body(db, &spec.symbol_name, spec.body, &mir_body)?;

    let runtime_abi = RuntimeAbi::source_shaped(
        mir_body.param_locals.len(),
        vec![None; mir_body.effect_param_locals.len()],
    );

    Ok(MirFunction {
        origin: MirFunctionOrigin::Synthetic(spec.id),
        body: mir_body,
        typed_body: Some(spec.typed_body),
        generic_args: Vec::new(),
        ret_ty: spec.ret_ty,
        returns_value: spec.returns_value,
        runtime_abi,
        runtime_return_shape: spec.runtime_return_shape,
        runtime_return_pointer_leaf_infos: Vec::new(),
        contract_function: None,
        inline_hint: Some(InlineHint::Never),
        symbol_name: spec.symbol_name,
        symbol_source: SymbolSource::Internal,
        receiver_space: None,
        defer_root: false,
    })
}

struct HandlerFinishSpec<'db> {
    body: hir::hir_def::Body<'db>,
    typed_body: hir::analysis::ty::ty_check::TypedBody<'db>,
    id: SyntheticId<'db>,
    ret_ty: TyId<'db>,
    return_behavior: ReturnBehavior,
    runtime_return_shape: RuntimeShape<'db>,
    returns_value: bool,
    symbol_name: String,
}

fn seed_effect_param_locals<'db>(
    db: &'db dyn HirAnalysisDb,
    builder: &mut MirBuilder<'db, '_>,
    contract: hir::hir_def::Contract<'db>,
    effects: &[EffectBinding<'db>],
) {
    let fields = contract.fields(db);
    let core = CoreLib::new(db, contract.scope());
    for effect in effects {
        let name = effect.binding_name.data(db).to_string();
        let binding = match effect.source {
            EffectSource::Root => LocalBinding::EffectParam {
                site: effect.binding_site,
                idx: effect.binding_idx as usize,
                key_path: effect.binding_path,
                is_mut: effect.is_mut,
            },
            EffectSource::Field(field_idx) => {
                let ty = fields
                    .get_index(field_idx as usize)
                    .map(|(_, field)| field.target_ty)
                    .unwrap_or_else(|| TyId::invalid(db, InvalidCause::Other));
                LocalBinding::Param {
                    site: ParamSite::EffectField(effect.binding_site),
                    idx: effect.binding_idx as usize,
                    mode: FuncParamMode::View,
                    ty,
                    is_mut: effect.is_mut,
                }
            }
        };
        let address_space = match effect.source {
            EffectSource::Root => AddressSpaceKind::Storage,
            EffectSource::Field(field_idx) => match fields.get_index(field_idx as usize) {
                Some((_, field)) if field.is_provider => {
                    repr::effect_provider_space_for_ty(db, &core, field.declared_ty)
                        .unwrap_or(AddressSpaceKind::Storage)
                }
                _ => AddressSpaceKind::Storage,
            },
        };
        builder.seed_synthetic_effect_param_local(name, binding, address_space);
    }
}

fn abi_payload_is_empty(db: &dyn HirAnalysisDb, ty: TyId<'_>) -> bool {
    layout::is_zero_sized_ty(db, ty)
}

fn init_handler_has_observable_effects<'db>(body: &MirBody<'db>) -> bool {
    body.blocks.iter().any(|block| {
        block.insts.iter().any(|inst| {
            matches!(
                inst,
                MirInst::Assign {
                    rvalue: Rvalue::Call(_) | Rvalue::Intrinsic { .. },
                    ..
                } | MirInst::Store { .. }
                    | MirInst::InitAggregate { .. }
                    | MirInst::SetDiscriminant { .. }
            )
        }) || matches!(
            block.terminator,
            Terminator::TerminatingCall { .. }
                | Terminator::Branch { .. }
                | Terminator::Switch { .. }
                | Terminator::Goto { .. }
                | Terminator::Unreachable { .. }
        )
    })
}

fn prune_redundant_fresh_storage_zero_stores<'db>(body: &mut MirBody<'db>) {
    if body.blocks.len() != 1
        || body.blocks[0].insts.iter().any(|inst| {
            matches!(
                inst,
                MirInst::Assign {
                    rvalue: Rvalue::Call(_) | Rvalue::Intrinsic { .. } | Rvalue::Load { .. },
                    ..
                } | MirInst::InitAggregate { .. }
                    | MirInst::SetDiscriminant { .. }
                    | MirInst::BindValue { .. }
            )
        })
    {
        return;
    }

    let insts = std::mem::take(&mut body.blocks[0].insts);
    let mut dirty_places = Vec::<(LocalId, MirProjectionPath<'db>)>::new();
    let mut rewritten = Vec::with_capacity(insts.len());
    for inst in insts {
        let MirInst::Store {
            source,
            place,
            value,
        } = inst
        else {
            rewritten.push(inst);
            continue;
        };

        let Some((local, path)) = static_storage_place_path(body, &place) else {
            rewritten.push(MirInst::Store {
                source,
                place,
                value,
            });
            continue;
        };

        if value_is_zero_literal(body, value)
            && !dirty_places.iter().any(|(dirty_local, dirty_path)| {
                storage_places_overlap(*dirty_local, dirty_path, local, &path)
            })
        {
            continue;
        }

        dirty_places.push((local, path));
        rewritten.push(MirInst::Store {
            source,
            place,
            value,
        });
    }
    body.blocks[0].insts = rewritten;
}

fn static_storage_place_path<'db>(
    body: &MirBody<'db>,
    place: &Place<'db>,
) -> Option<(LocalId, MirProjectionPath<'db>)> {
    if body.place_address_space(place) != AddressSpaceKind::Storage {
        return None;
    }
    let (local, prefix) = crate::ir::resolve_local_projection_root(&body.values, place.base)?;
    if projection_path_has_deref(&prefix)
        || projection_path_has_deref(&place.projection)
        || projection_path_has_index(&prefix)
        || projection_path_has_index(&place.projection)
    {
        return None;
    }
    Some((local, prefix.concat(&place.projection)))
}

fn storage_places_overlap<'db>(
    lhs_local: LocalId,
    lhs_path: &MirProjectionPath<'db>,
    rhs_local: LocalId,
    rhs_path: &MirProjectionPath<'db>,
) -> bool {
    lhs_local == rhs_local
        && (projection_path_is_prefix(lhs_path, rhs_path)
            || projection_path_is_prefix(rhs_path, lhs_path))
}

fn projection_path_is_prefix<'db>(
    prefix: &MirProjectionPath<'db>,
    full: &MirProjectionPath<'db>,
) -> bool {
    prefix.len() <= full.len() && prefix.iter().zip(full.iter()).all(|(lhs, rhs)| lhs == rhs)
}

fn projection_path_has_deref<'db>(path: &MirProjectionPath<'db>) -> bool {
    path.iter()
        .any(|proj| matches!(proj, hir::projection::Projection::Deref))
}

fn projection_path_has_index<'db>(path: &MirProjectionPath<'db>) -> bool {
    path.iter()
        .any(|proj| matches!(proj, hir::projection::Projection::Index(_)))
}

fn value_is_zero_literal<'db>(body: &MirBody<'db>, value: ValueId) -> bool {
    match &body.value(value).origin {
        ValueOrigin::Synthetic(SyntheticValue::Int(int)) => *int == num_bigint::BigUint::from(0u8),
        ValueOrigin::Synthetic(SyntheticValue::Bool(false)) | ValueOrigin::Unit => true,
        ValueOrigin::TransparentCast { value } => value_is_zero_literal(body, *value),
        _ => false,
    }
}
