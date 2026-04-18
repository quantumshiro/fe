//! Instruction-level lowering from MIR to Sonatina IR.
//!
//! Contains all `lower_*` free functions that operate on `LowerCtx`.

/// Solidity `Panic(uint256)` selector: `keccak256("Panic(uint256)")[:4]`.
///
/// Stored as a 32-byte big-endian word with the selector left-aligned,
/// ready for an EVM `MSTORE` at offset 0.
const PANIC_SELECTOR_WORD: [u8; 32] = {
    let mut bytes = [0u8; 32];
    bytes[0] = 0x4e;
    bytes[1] = 0x48;
    bytes[2] = 0x7b;
    bytes[3] = 0x71;
    bytes
};

/// Panic code for arithmetic overflow / underflow.
const PANIC_CODE_OVERFLOW: u64 = 0x11;

/// Panic code for division or modulo by zero.
const PANIC_CODE_DIVISION_BY_ZERO: u64 = 0x12;

/// Panic code for array index out of bounds.
const PANIC_CODE_INDEX_OUT_OF_BOUNDS: u64 = 0x32;

use common::ingot::IngotKind;
use driver::DriverDataBase;
use hir::analysis::ty::adt_def::AdtRef;
use hir::analysis::ty::normalize::normalize_ty;
use hir::analysis::ty::pattern_ir::ConstructorKind;
use hir::analysis::ty::trait_resolution::PredicateListId;
use hir::analysis::ty::ty_def::{CapabilityKind, PrimTy, TyBase, TyData, TyId};
use hir::hir_def::expr::{ArithBinOp, BinOp, CompBinOp, LogicalBinOp, UnOp};
use hir::projection::{IndexSource, Projection};
use mir::ir::{
    AddressSpaceKind, BuiltinTerminatorKind, CheckedArithmeticOp, CheckedIntrinsic, IntrinsicOp,
    Place, PointerInfo, SyntheticValue,
};
use mir::layout;
use mir::layout::TargetDataLayout;
use mir::repr::{PlaceState, ResolvedPlace, ResolvedPlaceProjection, ResolvedPlaceSegment};
use num_bigint::BigUint;
use rustc_hash::FxHashMap;
use smallvec1::SmallVec;
use sonatina_ir::{
    BlockId, GlobalVariableData, GlobalVariableRef, I256, Immediate, Linkage, Type, Value, ValueId,
    builder::ModuleBuilder,
    global_variable::GvInitializer,
    inst::{
        arith::{Add, Mul, Neg, Sar, Shl, Shr, Sub},
        cast::{Bitcast, IntToPtr, PtrToInt, Sext, Trunc, Zext},
        cmp::{Eq, Gt, IsZero, Lt, Ne, Slt},
        control_flow::{Br, BrTable, Call, Jump, Return},
        data::{
            Alloca, EnumAssertVariantRef, EnumGetTag, EnumProj, EnumSetTag, Gep, Mload, Mstore,
            ObjAlloc, ObjIndex, ObjLoad, ObjMaterializeStack, ObjProj, ObjStore, SymAddr, SymSize,
            SymbolRef,
        },
        evm::{
            EvmAddMod, EvmAddress, EvmBaseFee, EvmBlockHash, EvmByte, EvmCall, EvmCallValue,
            EvmCalldataCopy, EvmCalldataLoad, EvmCalldataSize, EvmCaller, EvmChainId, EvmCodeCopy,
            EvmCodeSize, EvmCoinBase, EvmCreate, EvmCreate2, EvmDelegateCall, EvmExp, EvmGas,
            EvmGasLimit, EvmInvalid, EvmKeccak256, EvmLog0, EvmLog1, EvmLog2, EvmLog3, EvmLog4,
            EvmMalloc, EvmMsize, EvmMstore8, EvmMulMod, EvmNumber, EvmOrigin, EvmPrevRandao,
            EvmReturn, EvmReturnDataCopy, EvmReturnDataSize, EvmRevert, EvmSelfBalance,
            EvmSelfDestruct, EvmSload, EvmSstore, EvmStaticCall, EvmStop, EvmTimestamp, EvmTload,
            EvmTstore, EvmUdiv, EvmUmod,
        },
        logic::{And, Not, Or, Xor},
    },
    module::FuncRef,
    object::EmbedSymbol,
    types::{EnumReprHint, EnumVariantRef, VariantData},
};

use super::{
    LowerCtx, LowerError, MaterializedLocalPlaceRoot, is_erased_runtime_ty, types,
    zero_value_for_type,
};

pub(super) struct TypeLowerer<'a, 'db> {
    builder: &'a ModuleBuilder,
    db: &'db DriverDataBase,
    core: &'a mir::CoreLib<'db>,
    target_layout: &'a TargetDataLayout,
    cache: &'a mut FxHashMap<String, Option<Type>>,
    name_counter: &'a mut usize,
}

impl<'a, 'db> TypeLowerer<'a, 'db> {
    pub(super) fn new(
        builder: &'a ModuleBuilder,
        db: &'db DriverDataBase,
        core: &'a mir::CoreLib<'db>,
        target_layout: &'a TargetDataLayout,
        cache: &'a mut FxHashMap<String, Option<Type>>,
        name_counter: &'a mut usize,
    ) -> Self {
        Self {
            builder,
            db,
            core,
            target_layout,
            cache,
            name_counter,
        }
    }

    pub(super) fn is_obj_ref(&self, ty: Type) -> bool {
        ty.is_obj_ref(&self.builder.ctx)
    }
}

/// Lower a MIR instruction.
pub(super) fn lower_instruction<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    inst: &mir::MirInst<'db>,
) -> Result<(), LowerError> {
    use mir::MirInst;

    match inst {
        MirInst::Assign { dest, rvalue, .. } => {
            if let mir::Rvalue::Alloc { address_space } = rvalue {
                let Some(dest_local) = dest else {
                    return Err(LowerError::Internal(
                        "alloc rvalue without destination local".to_string(),
                    ));
                };
                let value = lower_alloc(ctx, *dest_local, *address_space)?;
                write_local_result(ctx, *dest_local, value)?;
                return Ok(());
            }

            if let mir::Rvalue::ConstAggregate { data, ty } = rvalue {
                let Some(dest_local) = dest else {
                    return Err(LowerError::Internal(
                        "ConstAggregate without destination local".to_string(),
                    ));
                };
                let value = lower_const_aggregate(ctx, *dest_local, *ty, data)?;
                write_local_result(ctx, *dest_local, value)?;
                return Ok(());
            }
            let result = lower_rvalue(ctx, rvalue, *dest)?;
            if let (Some(dest_local), Some(result_val)) = (dest, result) {
                write_local_result(ctx, *dest_local, result_val)?;
            }
        }
        MirInst::Store { place, value, .. } => {
            lower_store_inst(ctx, place, *value)?;
        }
        MirInst::InitAggregate { place, inits, .. } => {
            for (path, value) in inits {
                let mut target = place.clone();
                for proj in path.iter() {
                    target.projection.push(proj.clone());
                }
                lower_store_inst(ctx, &target, *value)?;
            }
        }
        MirInst::SetDiscriminant { place, variant, .. } => {
            if !lower_enum_set_tag_for_place(ctx, place, *variant)? {
                let val = ctx.fb.make_imm_value(I256::from(variant.idx as u64));
                let discr_ty = TyId::new(ctx.db, TyData::TyBase(TyBase::Prim(PrimTy::U256)));
                store_typed_to_place(ctx, place, val, discr_ty)?;
            }
        }
        MirInst::BindValue { value, .. } => {
            // Ensure the value is lowered and cached
            let _ = lower_value(ctx, *value)?;
        }
    }

    Ok(())
}

fn local_place_root_layout<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Option<mir::ir::LocalPlaceRootLayout<'db>> {
    ctx.body
        .locals
        .get(local.index())
        .map(|local| local.place_root_layout)
}

fn materialized_local_place_root<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Option<MaterializedLocalPlaceRoot> {
    local_place_root_layout(ctx, local)
        .filter(|layout| layout.is_materialized())
        .and_then(|_| ctx.materialized_local_place_roots.get(&local).copied())
}

fn store_runtime_value_to_local_place_root<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
    place_root: MaterializedLocalPlaceRoot,
    value: ValueId,
) -> Result<(), LowerError> {
    match place_root {
        MaterializedLocalPlaceRoot::MemorySlot(slot_ptr) => {
            store_runtime_value_to_local_slot_ptr(ctx, local, slot_ptr, value)
        }
        MaterializedLocalPlaceRoot::ObjectRoot(object_ref) => {
            let local_ty = ctx
                .body
                .locals
                .get(local.index())
                .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
                .ty;
            let object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
            let stored = coerce_value_to_runtime_ty(ctx, value, local_ty, object_elem_ty);
            ctx.fb
                .insert_inst_no_result(ObjStore::new(ctx.is, object_ref, stored));
            Ok(())
        }
    }
}

fn write_local_result<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    dest_local: mir::LocalId,
    value: ValueId,
) -> Result<(), LowerError> {
    let dest_ty = ctx
        .body
        .locals
        .get(dest_local.index())
        .ok_or_else(|| LowerError::Internal(format!("missing local type for {dest_local:?}")))?
        .ty;
    let dest_var = ctx.local_vars.get(&dest_local).copied().ok_or_else(|| {
        LowerError::Internal(format!("missing SSA variable for local {dest_local:?}"))
    })?;
    let expected_runtime_ty = ctx.local_runtime_types[dest_local.index()];
    let value = coerce_value_to_runtime_ty(ctx, value, dest_ty, expected_runtime_ty);
    ctx.fb.def_var(dest_var, value);
    ctx.initialized_locals.insert(dest_local);
    if let Some(place_root) = materialized_local_place_root(ctx, dest_local) {
        store_runtime_value_to_local_place_root(ctx, dest_local, place_root, value)?;
    }
    Ok(())
}

fn current_local_runtime_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Result<ValueId, LowerError> {
    let var =
        ctx.local_vars.get(&local).copied().ok_or_else(|| {
            LowerError::Internal(format!("missing SSA variable for local {local:?}"))
        })?;
    Ok(ctx.fb.use_var(var))
}

fn allocate_local_place_root_slot<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Result<ValueId, LowerError> {
    if local_place_root_layout(ctx, local).is_some_and(|layout| layout.is_object_root()) {
        return Err(LowerError::Internal(format!(
            "object-backed local {local:?} must not use a synthetic place-root slot"
        )));
    }

    let local_ty = ctx
        .body
        .locals
        .get(local.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
        .ty;
    let Some(size_bytes) = layout::ty_memory_size_or_word_in(ctx.db, ctx.target_layout, local_ty)
    else {
        return Err(LowerError::Unsupported(format!(
            "cannot determine addressable slot size for `{}`",
            local_ty.pretty_print(ctx.db)
        )));
    };
    let opaque_ptr_ty = ctx.fb.ptr_type(Type::I8);
    if size_bytes == 0 {
        let zero = types::zero_value(ctx.fb, Type::I256);
        return Ok(ctx
            .fb
            .insert_inst(IntToPtr::new(ctx.is, zero, opaque_ptr_ty), opaque_ptr_ty));
    }
    let alloca_ty = ctx.fb.declare_array_type(Type::I8, size_bytes);
    Ok(emit_alloca_ptr(ctx.fb, alloca_ty, ctx.is))
}

fn store_runtime_value_to_local_slot_ptr<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
    slot_ptr: ValueId,
    value: ValueId,
) -> Result<(), LowerError> {
    let local_ty = ctx
        .body
        .locals
        .get(local.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
        .ty;
    if is_erased_runtime_ty(ctx.db, ctx.target_layout, local_ty) {
        return Ok(());
    }
    let ptr_ty = ctx.fb.ptr_type(Type::I8);
    let slot_ptr = bitcast_ptr(ctx, slot_ptr, ptr_ty);
    let value_ty = ctx.fb.type_of(value);
    if value_ty.is_pointer(&ctx.fb.module_builder.ctx) {
        ctx.fb
            .insert_inst_no_result(Mstore::new(ctx.is, slot_ptr, value, value_ty));
        return Ok(());
    }
    let word = apply_to_word(ctx.fb, ctx.db, value, local_ty, ctx.is);
    ctx.fb
        .insert_inst_no_result(Mstore::new(ctx.is, slot_ptr, word, Type::I256));
    Ok(())
}

pub(super) fn ensure_local_place_root_slot<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Result<ValueId, LowerError> {
    if let Some(place_root) = ctx.materialized_local_place_roots.get(&local).copied() {
        return match place_root {
            MaterializedLocalPlaceRoot::MemorySlot(slot_ptr) => Ok(slot_ptr),
            MaterializedLocalPlaceRoot::ObjectRoot(_) => Err(LowerError::Internal(format!(
                "object-backed place root already exists for local {local:?}"
            ))),
        };
    }

    let slot_ptr = allocate_local_place_root_slot(ctx, local)?;
    if ctx.initialized_locals.contains(&local) {
        let current = current_local_runtime_value(ctx, local)?;
        store_runtime_value_to_local_slot_ptr(ctx, local, slot_ptr, current)?;
    }
    ctx.materialized_local_place_roots
        .insert(local, MaterializedLocalPlaceRoot::MemorySlot(slot_ptr));
    Ok(slot_ptr)
}

fn ensure_local_place_root_object<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
) -> Result<ValueId, LowerError> {
    if let Some(place_root) = ctx.materialized_local_place_roots.get(&local).copied() {
        return match place_root {
            MaterializedLocalPlaceRoot::ObjectRoot(object_ref) => Ok(object_ref),
            MaterializedLocalPlaceRoot::MemorySlot(_) => Err(LowerError::Internal(format!(
                "memory place-root slot already exists for object-backed local {local:?}"
            ))),
        };
    }

    let local_ty = ctx
        .body
        .locals
        .get(local.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
        .ty;
    let Some(target_ty) = local_place_root_layout(ctx, local)
        .filter(|layout| {
            matches!(
                layout,
                mir::ir::LocalPlaceRootLayout::ObjectRootStorage { .. }
            )
        })
        .and_then(|layout| layout.object_target_ty())
    else {
        return Err(LowerError::Internal(format!(
            "local {local:?} `{}` does not use a materialized object-backed place root",
            local_ty.pretty_print(ctx.db),
        )));
    };
    let current = if ctx.initialized_locals.contains(&local) {
        Some(current_local_runtime_value(ctx, local)?)
    } else {
        None
    };
    let size_bytes = layout::ty_memory_size_or_word_in(ctx.db, ctx.target_layout, target_ty)
        .ok_or_else(|| {
            LowerError::Unsupported(format!(
                "cannot determine object root size for `{}`",
                target_ty.pretty_print(ctx.db),
            ))
        })?;
    let object_ty = ctx
        .type_lowerer()
        .fe_object_ty_to_sonatina_with_pointer_leaf_infos(target_ty, &[])
        .unwrap_or_else(|| ctx.fb.declare_array_type(Type::I8, size_bytes));
    let object_ref = emit_obj_alloc_ref(ctx.fb, object_ty, ctx.is);
    if let Some(current) = current {
        store_runtime_value_to_local_place_root(
            ctx,
            local,
            MaterializedLocalPlaceRoot::ObjectRoot(object_ref),
            current,
        )?;
    }
    ctx.materialized_local_place_roots
        .insert(local, MaterializedLocalPlaceRoot::ObjectRoot(object_ref));
    Ok(object_ref)
}

fn load_runtime_value_from_local_slot<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
    expected_runtime_ty: Type,
) -> Result<ValueId, LowerError> {
    let slot_ptr = ensure_local_place_root_slot(ctx, local)?;
    let local_ty = ctx
        .body
        .locals
        .get(local.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
        .ty;
    if expected_runtime_ty.is_pointer(&ctx.fb.module_builder.ctx) {
        return Ok(ctx.fb.insert_inst(
            Mload::new(ctx.is, slot_ptr, expected_runtime_ty),
            expected_runtime_ty,
        ));
    }
    let raw = ctx
        .fb
        .insert_inst(Mload::new(ctx.is, slot_ptr, Type::I256), Type::I256);
    let loaded = apply_from_word(ctx.fb, ctx.db, raw, local_ty, ctx.is);
    Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty))
}

fn load_runtime_value_from_local_place_root<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    local: mir::LocalId,
    place_root: MaterializedLocalPlaceRoot,
    expected_runtime_ty: Type,
) -> Result<ValueId, LowerError> {
    match place_root {
        MaterializedLocalPlaceRoot::MemorySlot(_) => {
            load_runtime_value_from_local_slot(ctx, local, expected_runtime_ty)
        }
        MaterializedLocalPlaceRoot::ObjectRoot(object_ref) => {
            let local_ty = ctx
                .body
                .locals
                .get(local.index())
                .ok_or_else(|| LowerError::Internal(format!("unknown local: {local:?}")))?
                .ty;
            let object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
            let loaded = ctx
                .fb
                .insert_inst(ObjLoad::new(ctx.is, object_ref), object_elem_ty);
            Ok(coerce_value_to_runtime_ty(
                ctx,
                loaded,
                local_ty,
                expected_runtime_ty,
            ))
        }
    }
}

/// Lower a MIR rvalue to a Sonatina value.
fn lower_rvalue<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    rvalue: &mir::Rvalue<'db>,
    dest_local: Option<mir::LocalId>,
) -> Result<Option<ValueId>, LowerError> {
    use mir::Rvalue;

    match rvalue {
        Rvalue::ZeroInit => {
            let ty = dest_local
                .map(|local| ctx.local_runtime_types[local.index()])
                .unwrap_or(Type::I256);
            Ok(Some(zero_value_for_type(ctx.fb, ty, ctx.is)))
        }
        Rvalue::Value(value_id) => {
            let val = lower_value(ctx, *value_id)?;
            Ok(Some(val))
        }
        Rvalue::Call(call) => {
            if let Some(checked) = call.checked_intrinsic {
                if !call.effect_args.is_empty() {
                    return Err(LowerError::Internal(format!(
                        "checked intrinsic call unexpectedly has effect args: {checked:?}"
                    )));
                }
                let result = lower_checked_intrinsic(ctx, checked, &call.args)?;
                return Ok(Some(result));
            }
            if let Some(result) = try_lower_generic_saturating_intrinsic(ctx, call)? {
                return Ok(Some(result));
            }

            // Builtin terminators (Abort / AbortWithValue) that appear as regular
            // call instructions (due to never-type coercion in match arms).
            if let Some(builtin) = call.builtin_terminator {
                match builtin {
                    BuiltinTerminatorKind::Abort | BuiltinTerminatorKind::AbortWithValue => {
                        let zero = ctx.fb.make_imm_value(I256::zero());
                        ctx.fb
                            .insert_inst_no_result(EvmRevert::new(ctx.is, zero, zero));
                        return Ok(None);
                    }
                }
            }

            // Get the callee function reference
            let callee_name = call.resolved_name.as_ref().ok_or_else(|| {
                LowerError::Unsupported("call without resolved symbol name".to_string())
            })?;

            if call.effect_args.is_empty() {
                // `std::evm::ops` externs (Yul builtins).
                //
                // These are declared in Fe as `extern`, so they do not have MIR bodies. The Yul
                // backend emits them as builtins; the Sonatina backend must lower them directly.
                match callee_name.as_str() {
                    // Logs
                    "log0" | "log1" | "log2" | "log3" | "log4" => {
                        let mut args = Vec::with_capacity(call.args.len());
                        for &arg in &call.args {
                            args.push(lower_value(ctx, arg)?);
                        }
                        match (callee_name.as_str(), args.as_slice()) {
                            ("log0", [offset, len]) => {
                                let offset = coerce_value_to_word(ctx, *offset);
                                ctx.fb
                                    .insert_inst_no_result(EvmLog0::new(ctx.is, offset, *len));
                                return Ok(None);
                            }
                            ("log1", [offset, len, topic0]) => {
                                let offset = coerce_value_to_word(ctx, *offset);
                                ctx.fb.insert_inst_no_result(EvmLog1::new(
                                    ctx.is, offset, *len, *topic0,
                                ));
                                return Ok(None);
                            }
                            ("log2", [offset, len, topic0, topic1]) => {
                                let offset = coerce_value_to_word(ctx, *offset);
                                ctx.fb.insert_inst_no_result(EvmLog2::new(
                                    ctx.is, offset, *len, *topic0, *topic1,
                                ));
                                return Ok(None);
                            }
                            ("log3", [offset, len, topic0, topic1, topic2]) => {
                                let offset = coerce_value_to_word(ctx, *offset);
                                ctx.fb.insert_inst_no_result(EvmLog3::new(
                                    ctx.is, offset, *len, *topic0, *topic1, *topic2,
                                ));
                                return Ok(None);
                            }
                            ("log4", [offset, len, topic0, topic1, topic2, topic3]) => {
                                let offset = coerce_value_to_word(ctx, *offset);
                                ctx.fb.insert_inst_no_result(EvmLog4::new(
                                    ctx.is, offset, *len, *topic0, *topic1, *topic2, *topic3,
                                ));
                                return Ok(None);
                            }
                            _ => {
                                return Err(LowerError::Internal(format!(
                                    "{callee_name} expects {} args, got {}",
                                    match callee_name.as_str() {
                                        "log0" => 2,
                                        "log1" => 3,
                                        "log2" => 4,
                                        "log3" => 5,
                                        "log4" => 6,
                                        _ => unreachable!(),
                                    },
                                    args.len()
                                )));
                            }
                        }
                    }

                    // Environment
                    "address" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmAddress::new(ctx.is), Type::I256),
                        ));
                    }
                    "callvalue" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmCallValue::new(ctx.is), Type::I256),
                        ));
                    }
                    "origin" => {
                        return Ok(Some(ctx.fb.insert_inst(EvmOrigin::new(ctx.is), Type::I256)));
                    }
                    "gasprice" => {
                        return Err(LowerError::Unsupported(
                            "gasprice is not supported by the Sonatina backend".to_string(),
                        ));
                    }
                    "coinbase" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmCoinBase::new(ctx.is), Type::I256),
                        ));
                    }
                    "timestamp" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmTimestamp::new(ctx.is), Type::I256),
                        ));
                    }
                    "number" => {
                        return Ok(Some(ctx.fb.insert_inst(EvmNumber::new(ctx.is), Type::I256)));
                    }
                    "prevrandao" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmPrevRandao::new(ctx.is), Type::I256),
                        ));
                    }
                    "gaslimit" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmGasLimit::new(ctx.is), Type::I256),
                        ));
                    }
                    "chainid" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmChainId::new(ctx.is), Type::I256),
                        ));
                    }
                    "basefee" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmBaseFee::new(ctx.is), Type::I256),
                        ));
                    }
                    "selfbalance" => {
                        return Ok(Some(
                            ctx.fb.insert_inst(EvmSelfBalance::new(ctx.is), Type::I256),
                        ));
                    }
                    "blockhash" => {
                        let [block] = call.args.as_slice() else {
                            return Err(LowerError::Internal(
                                "blockhash requires 1 argument".to_string(),
                            ));
                        };
                        let block = lower_value(ctx, *block)?;
                        return Ok(Some(
                            ctx.fb
                                .insert_inst(EvmBlockHash::new(ctx.is, block), Type::I256),
                        ));
                    }
                    "gas" => return Ok(Some(ctx.fb.insert_inst(EvmGas::new(ctx.is), Type::I256))),

                    // Memory size
                    "msize" => {
                        return Ok(Some(ctx.fb.insert_inst(EvmMsize::new(ctx.is), Type::I256)));
                    }

                    // Calls / create
                    "create" => {
                        let [val, offset, len] = call.args.as_slice() else {
                            return Err(LowerError::Internal(
                                "create requires 3 arguments".to_string(),
                            ));
                        };
                        let val = lower_value(ctx, *val)?;
                        let offset = lower_value(ctx, *offset)?;
                        let len = lower_value(ctx, *len)?;
                        let offset = coerce_value_to_word(ctx, offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmCreate::new(ctx.is, val, offset, len),
                            Type::I256,
                        )));
                    }
                    "create2" => {
                        let [val, offset, len, salt] = call.args.as_slice() else {
                            return Err(LowerError::Internal(
                                "create2 requires 4 arguments".to_string(),
                            ));
                        };
                        let val = lower_value(ctx, *val)?;
                        let offset = lower_value(ctx, *offset)?;
                        let len = lower_value(ctx, *len)?;
                        let salt = lower_value(ctx, *salt)?;
                        let offset = coerce_value_to_word(ctx, offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmCreate2::new(ctx.is, val, offset, len, salt),
                            Type::I256,
                        )));
                    }
                    "call" => {
                        let [gas, addr, val, arg_offset, arg_len, ret_offset, ret_len] =
                            call.args.as_slice()
                        else {
                            return Err(LowerError::Internal(
                                "call requires 7 arguments".to_string(),
                            ));
                        };
                        let gas = lower_value(ctx, *gas)?;
                        let addr = lower_value(ctx, *addr)?;
                        let val = lower_value(ctx, *val)?;
                        let arg_offset = lower_value(ctx, *arg_offset)?;
                        let arg_len = lower_value(ctx, *arg_len)?;
                        let ret_offset = lower_value(ctx, *ret_offset)?;
                        let ret_len = lower_value(ctx, *ret_len)?;
                        let arg_offset = coerce_value_to_word(ctx, arg_offset);
                        let ret_offset = coerce_value_to_word(ctx, ret_offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmCall::new(
                                ctx.is, gas, addr, val, arg_offset, arg_len, ret_offset, ret_len,
                            ),
                            Type::I256,
                        )));
                    }
                    "staticcall" => {
                        let [gas, addr, arg_offset, arg_len, ret_offset, ret_len] =
                            call.args.as_slice()
                        else {
                            return Err(LowerError::Internal(
                                "staticcall requires 6 arguments".to_string(),
                            ));
                        };
                        let gas = lower_value(ctx, *gas)?;
                        let addr = lower_value(ctx, *addr)?;
                        let arg_offset = lower_value(ctx, *arg_offset)?;
                        let arg_len = lower_value(ctx, *arg_len)?;
                        let ret_offset = lower_value(ctx, *ret_offset)?;
                        let ret_len = lower_value(ctx, *ret_len)?;
                        let arg_offset = coerce_value_to_word(ctx, arg_offset);
                        let ret_offset = coerce_value_to_word(ctx, ret_offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmStaticCall::new(
                                ctx.is, gas, addr, arg_offset, arg_len, ret_offset, ret_len,
                            ),
                            Type::I256,
                        )));
                    }
                    "delegatecall" => {
                        let [gas, addr, arg_offset, arg_len, ret_offset, ret_len] =
                            call.args.as_slice()
                        else {
                            return Err(LowerError::Internal(
                                "delegatecall requires 6 arguments".to_string(),
                            ));
                        };
                        let gas = lower_value(ctx, *gas)?;
                        let addr = lower_value(ctx, *addr)?;
                        let arg_offset = lower_value(ctx, *arg_offset)?;
                        let arg_len = lower_value(ctx, *arg_len)?;
                        let ret_offset = lower_value(ctx, *ret_offset)?;
                        let ret_len = lower_value(ctx, *ret_len)?;
                        let arg_offset = coerce_value_to_word(ctx, arg_offset);
                        let ret_offset = coerce_value_to_word(ctx, ret_offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmDelegateCall::new(
                                ctx.is, gas, addr, arg_offset, arg_len, ret_offset, ret_len,
                            ),
                            Type::I256,
                        )));
                    }
                    _ => {}
                }
            }

            // Special-case a few thin std wrappers that are semantically EVM opcodes.
            //
            // These wrappers show up as regular MIR functions (not `extern`), but in the Sonatina
            // backend we prefer to lower them directly to opcodes to avoid depending on internal
            // call return-value plumbing for correctness.
            if call.effect_args.is_empty() {
                match callee_name.as_str() {
                    "alloc" => {
                        let [size] = call.args.as_slice() else {
                            return Err(LowerError::Internal(
                                "alloc expects 1 argument (size)".to_string(),
                            ));
                        };
                        let size_ty = ctx
                            .body
                            .values
                            .get(size.index())
                            .ok_or_else(|| {
                                LowerError::Internal("unknown call argument".to_string())
                            })?
                            .ty;
                        if is_erased_runtime_ty(ctx.db, ctx.target_layout, size_ty) {
                            return Err(LowerError::Internal(
                                "alloc size argument unexpectedly erased".to_string(),
                            ));
                        }
                        let size = lower_value(ctx, *size)?;
                        return Ok(Some(emit_evm_malloc_word_addr(ctx.fb, size, ctx.is)));
                    }
                    "evm_create_create_raw" => {
                        let mut lowered = Vec::new();
                        for &arg in &call.args {
                            let arg_ty = ctx
                                .body
                                .values
                                .get(arg.index())
                                .ok_or_else(|| {
                                    LowerError::Internal("unknown call argument".to_string())
                                })?
                                .ty;
                            if is_erased_runtime_ty(ctx.db, ctx.target_layout, arg_ty) {
                                continue;
                            }
                            lowered.push(lower_value(ctx, arg)?);
                        }

                        let [val, offset, len] = lowered.as_slice() else {
                            return Err(LowerError::Internal(format!(
                                "{callee_name} expects 3 args (value, offset, len) after ZST erasure, got {}",
                                lowered.len()
                            )));
                        };
                        let offset = coerce_value_to_word(ctx, *offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmCreate::new(ctx.is, *val, offset, *len),
                            Type::I256,
                        )));
                    }
                    "evm_create_create2_raw" => {
                        let mut lowered = Vec::new();
                        for &arg in &call.args {
                            let arg_ty = ctx
                                .body
                                .values
                                .get(arg.index())
                                .ok_or_else(|| {
                                    LowerError::Internal("unknown call argument".to_string())
                                })?
                                .ty;
                            if is_erased_runtime_ty(ctx.db, ctx.target_layout, arg_ty) {
                                continue;
                            }
                            lowered.push(lower_value(ctx, arg)?);
                        }

                        let [val, offset, len, salt] = lowered.as_slice() else {
                            return Err(LowerError::Internal(format!(
                                "{callee_name} expects 4 args (value, offset, len, salt) after ZST erasure, got {}",
                                lowered.len()
                            )));
                        };
                        let offset = coerce_value_to_word(ctx, *offset);
                        return Ok(Some(ctx.fb.insert_inst(
                            EvmCreate2::new(ctx.is, *val, offset, *len, *salt),
                            Type::I256,
                        )));
                    }
                    _ => {}
                }
            }

            // Core numeric intrinsics (extern functions from `core::num`).
            if call.effect_args.is_empty()
                && let Some(result) = try_lower_numeric_intrinsic(ctx, callee_name, &call.args)?
            {
                return Ok(Some(result));
            }

            let func_ref = ctx
                .name_map
                .get(callee_name)
                .ok_or_else(|| LowerError::Internal(format!("unknown function: {callee_name}")))?;

            let args = lower_call_args(
                ctx,
                callee_name,
                &call.args,
                &call.effect_args,
                *func_ref,
                "call",
            )?;

            // Emit call instruction with proper return type
            let call_inst = Call::new(ctx.is, *func_ref, args.into());
            let callee_metadata =
                ctx.runtime_function_metadata
                    .get(callee_name)
                    .ok_or_else(|| {
                        LowerError::Internal(format!(
                            "missing runtime type metadata for function: {callee_name}"
                        ))
                    })?;
            if let Some(ret_ty) = callee_metadata.ret {
                let result = ctx.fb.insert_inst(call_inst, ret_ty);
                Ok(Some(result))
            } else {
                // Unit-returning calls don't produce a value
                ctx.fb.insert_inst_no_result(call_inst);
                Ok(None)
            }
        }
        Rvalue::Intrinsic { op, args } => lower_intrinsic(ctx, *op, args),
        Rvalue::Load { place } => {
            let expected_runtime_ty = dest_local
                .map(|local| ctx.local_runtime_types[local.index()])
                .unwrap_or(Type::I256);
            let loaded_ty = dest_local
                .and_then(|local| ctx.body.locals.get(local.index()))
                .map(|local| local.ty)
                .ok_or_else(|| {
                    LowerError::Internal("load rvalue without a destination local type".to_string())
                })?;
            Ok(Some(load_place_runtime(
                ctx,
                place,
                loaded_ty,
                expected_runtime_ty,
            )?))
        }
        Rvalue::Alloc { .. } => Err(LowerError::Internal(
            "Alloc rvalue should be handled directly in Assign lowering".to_string(),
        )),
        Rvalue::ConstAggregate { .. } => Err(LowerError::Unsupported(
            "ConstAggregate not yet supported in Sonatina backend".to_string(),
        )),
    }
}

/// Lower call arguments (regular + effect), applying the runtime parameter mask or
/// filtering erased types, then zero-padding to match the callee signature width.
fn lower_call_args<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    callee_name: &str,
    regular_args: &[mir::ValueId],
    effect_args: &[mir::ValueId],
    func_ref: FuncRef,
    context: &str,
) -> Result<Vec<ValueId>, LowerError> {
    let mut args = Vec::with_capacity(regular_args.len() + effect_args.len());
    let mut arg_tys = Vec::with_capacity(regular_args.len() + effect_args.len());
    if let Some(metadata) = ctx.runtime_function_metadata.get(callee_name) {
        let all_args: Vec<_> = regular_args
            .iter()
            .chain(effect_args.iter())
            .copied()
            .collect();
        if metadata.params.len() != all_args.len() {
            return Err(LowerError::Internal(format!(
                "{context} to `{callee_name}` has mismatched arg metadata length (params={}, call_args={})",
                metadata.params.len(),
                all_args.len()
            )));
        }
        for (expected_ty, arg) in metadata.params.iter().copied().zip(all_args) {
            let arg_ty = ctx
                .body
                .values
                .get(arg.index())
                .ok_or_else(|| LowerError::Internal("unknown call argument".to_string()))?
                .ty;
            let lowered = lower_value(ctx, arg)?;
            let lowered_ty = ctx.fb.type_of(lowered);
            if (lowered_ty.is_obj_ref(&ctx.fb.module_builder.ctx)
                || expected_ty.is_obj_ref(&ctx.fb.module_builder.ctx))
                && lowered_ty != expected_ty
            {
                let lowered_dbg = lowered_ty.resolve_compound(&ctx.fb.module_builder.ctx);
                let expected_dbg = expected_ty.resolve_compound(&ctx.fb.module_builder.ctx);
                return Err(LowerError::Internal(format!(
                    "{context} to `{callee_name}` lowered arg {arg:?} (`{}``) to object ref type {lowered_ty:?} {lowered_dbg:?}, expected {expected_ty:?} {expected_dbg:?}",
                    arg_ty.pretty_print(ctx.db),
                )));
            }
            args.push(coerce_value_to_runtime_ty(
                ctx,
                lowered,
                arg_ty,
                expected_ty,
            ));
            arg_tys.push(arg_ty);
        }
    } else {
        // Fallback for callees without a declared signature/mask (e.g. externs).
        for &arg in regular_args {
            let arg_ty = ctx
                .body
                .values
                .get(arg.index())
                .ok_or_else(|| LowerError::Internal("unknown call argument".to_string()))?
                .ty;
            if is_erased_runtime_ty(ctx.db, ctx.target_layout, arg_ty) {
                continue;
            }
            args.push(lower_value(ctx, arg)?);
            arg_tys.push(arg_ty);
        }
        for &effect_arg in effect_args {
            let arg_ty = ctx
                .body
                .values
                .get(effect_arg.index())
                .ok_or_else(|| LowerError::Internal("unknown call effect argument".to_string()))?
                .ty;
            if is_erased_runtime_ty(ctx.db, ctx.target_layout, arg_ty) {
                continue;
            }
            args.push(lower_value(ctx, effect_arg)?);
            arg_tys.push(arg_ty);
        }
    }

    let expected_arg_tys = ctx
        .fb
        .module_builder
        .ctx
        .func_sig(func_ref, |sig| sig.args().to_vec());
    let expected_argc = expected_arg_tys.len();
    if args.len() > expected_argc {
        return Err(LowerError::Internal(format!(
            "{context} to `{callee_name}` has too many args (got {}, expected {expected_argc})",
            args.len()
        )));
    }
    for ((arg, arg_ty), expected_ty) in args
        .iter_mut()
        .zip(arg_tys.iter().copied())
        .zip(expected_arg_tys.iter().copied())
    {
        *arg = coerce_runtime_value(ctx.fb, ctx.db, *arg, arg_ty, expected_ty, ctx.is);
    }
    for ty in expected_arg_tys.into_iter().skip(args.len()) {
        args.push(types::zero_value(ctx.fb, ty));
    }
    while args.len() < expected_argc {
        let arg_ty = ctx
            .fb
            .module_builder
            .ctx
            .func_sig(func_ref, |sig| sig.args()[args.len()]);
        args.push(zero_value_for_type(ctx.fb, arg_ty, ctx.is));
    }

    Ok(args)
}

/// Lower a MIR value to a Sonatina value.
fn lower_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value_id: mir::ValueId,
) -> Result<ValueId, LowerError> {
    let value_data = ctx.body.values.get(value_id.index()).ok_or_else(|| {
        LowerError::Internal(format!("unknown MIR value id {}", value_id.index()))
    })?;

    // Note: We intentionally avoid caching lowered MIR values across the function.
    //
    // Sonatina's SSA builder may rewrite/remove placeholder `phi`s during sealing; caching a value
    // that (transitively) comes from `use_var` can leave us holding a `ValueId` whose defining
    // instruction was removed from the layout, producing malformed IR.
    //
    // This can be revisited once we have a robust notion of which MIR values are stable across
    // blocks after SSA sealing.
    lower_value_origin(ctx, value_id, value_data)
}

/// Lower a MIR value origin to a Sonatina value.
fn lower_value_origin<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value_id: mir::ValueId,
    value_data: &mir::ValueData<'db>,
) -> Result<ValueId, LowerError> {
    use mir::ValueOrigin;
    let origin = &value_data.origin;
    let result_ty = match origin {
        ValueOrigin::PlaceRef(place) | ValueOrigin::MoveOut { place }
            if matches!(
                value_data.runtime_shape,
                mir::ir::RuntimeShape::EnumTag { .. }
            ) =>
        {
            split_place_discriminant_tail(place)
                .and_then(|owner_place| {
                    specialized_enum_tag_runtime_ty_for_place(ctx, &owner_place)
                })
                .unwrap_or_else(|| ctx.runtime_type_for_value(value_id))
        }
        _ => ctx.runtime_type_for_value(value_id),
    };

    match origin {
        ValueOrigin::Synthetic(syn) => match syn {
            SyntheticValue::Int(n) => {
                let i256_val = biguint_to_i256(n);
                Ok(ctx
                    .fb
                    .make_imm_value(Immediate::from_i256(i256_val, result_ty)))
            }
            SyntheticValue::Bool(b) => {
                if result_ty == Type::I1 {
                    Ok(ctx.fb.make_imm_value(*b))
                } else {
                    let val = if *b { I256::one() } else { I256::zero() };
                    Ok(ctx.fb.make_imm_value(Immediate::from_i256(val, result_ty)))
                }
            }
            SyntheticValue::Bytes(bytes) => {
                if bytes.len() > 32 {
                    return Err(LowerError::Unsupported(format!(
                        "SyntheticValue::Bytes must fit in one EVM word, got {} bytes",
                        bytes.len()
                    )));
                }
                // Convert bytes to I256 (left-padded to 32 bytes)
                let i256_val = bytes_to_i256(bytes);
                Ok(ctx.fb.make_imm_value(i256_val))
            }
        },
        ValueOrigin::Local(local_id) => {
            if let Some(place_root) = materialized_local_place_root(ctx, *local_id) {
                return load_runtime_value_from_local_place_root(
                    ctx, *local_id, place_root, result_ty,
                );
            }
            let var = ctx.local_vars.get(local_id).copied().ok_or_else(|| {
                LowerError::Internal(format!("SSA variable not found for local {local_id:?}"))
            })?;
            Ok(ctx.fb.use_var(var))
        }
        ValueOrigin::PlaceRoot(local_id) => {
            match local_place_root_layout(ctx, *local_id).ok_or_else(|| {
                LowerError::Internal(format!(
                    "missing local metadata for place root {local_id:?}"
                ))
            })? {
                mir::ir::LocalPlaceRootLayout::ObjectRootValue { .. } => {
                    let value = current_local_runtime_value(ctx, *local_id)?;
                    Ok(coerce_value_to_type(ctx, value, result_ty))
                }
                mir::ir::LocalPlaceRootLayout::ObjectRootStorage { .. } => {
                    let object_ref = ensure_local_place_root_object(ctx, *local_id)?;
                    Ok(coerce_value_to_type(ctx, object_ref, result_ty))
                }
                mir::ir::LocalPlaceRootLayout::MemorySlot => {
                    let slot_ptr = ensure_local_place_root_slot(ctx, *local_id)?;
                    Ok(coerce_value_to_type(ctx, slot_ptr, result_ty))
                }
                mir::ir::LocalPlaceRootLayout::Direct => Err(LowerError::Internal(format!(
                    "direct local {local_id:?} reached Sonatina place-root lowering without explicit runtime owner layout"
                ))),
            }
        }
        ValueOrigin::Unit => Ok(types::zero_value(ctx.fb, result_ty)),
        ValueOrigin::Unary { op, inner } => {
            let inner_val = lower_value(ctx, *inner)?;
            lower_unary_op(ctx.fb, ctx.db, *op, inner_val, value_data.ty, ctx.is)
        }
        ValueOrigin::Binary { op, lhs, rhs } => {
            let lhs_val = lower_value(ctx, *lhs)?;
            let rhs_val = lower_value(ctx, *rhs)?;
            let lhs_ty = ctx
                .body
                .values
                .get(lhs.index())
                .ok_or_else(|| {
                    LowerError::Internal(format!("unknown MIR value id {}", lhs.index()))
                })?
                .ty;
            lower_binary_op(ctx.fb, ctx.db, *op, lhs_val, rhs_val, lhs_ty, ctx.is)
        }
        ValueOrigin::TransparentCast { value } => {
            let inner_val = lower_value(ctx, *value)?;
            let inner_ty = ctx
                .body
                .values
                .get(value.index())
                .ok_or_else(|| {
                    LowerError::Internal(format!("unknown MIR value id {}", value.index()))
                })?
                .ty;
            Ok(coerce_runtime_value(
                ctx.fb, ctx.db, inner_val, inner_ty, result_ty, ctx.is,
            ))
        }
        ValueOrigin::ControlFlowResult { expr } => {
            // ControlFlowResult values should be converted to Local values during MIR lowering.
            // If we reach here, it means MIR lowering didn't properly handle this case.
            Err(LowerError::Internal(format!(
                "ControlFlowResult value reached codegen without being converted to Local (expr={expr:?})"
            )))
        }
        ValueOrigin::PlaceRef(place) => {
            if !value_data.repr.is_ref() {
                let loaded_ty = value_data
                    .ty
                    .as_capability(ctx.db)
                    .map(|(_, inner_ty)| inner_ty)
                    .unwrap_or(value_data.ty);
                if place_yields_location_value(
                    ctx,
                    place,
                    value_data.ty,
                    ctx.body.value_pointer_info(value_id),
                )? {
                    return lower_place_runtime_location_value(ctx, place, result_ty);
                }
                return load_place_runtime(ctx, place, loaded_ty, result_ty);
            }
            if value_data.repr.address_space() == Some(AddressSpaceKind::Memory) {
                return lower_place_runtime_location_value(ctx, place, result_ty);
            }
            lower_place_address(ctx, place)
        }
        ValueOrigin::MoveOut { place } => {
            if place.projection.is_empty()
                && move_out_uses_root_local_alias(&ctx.body.values, place.base)
                && place_yields_location_value(
                    ctx,
                    place,
                    value_data.ty,
                    ctx.body.value_pointer_info(value_id),
                )?
            {
                return lower_value(ctx, place.base);
            }

            if value_data.repr.is_ref()
                && value_data.repr.address_space() == Some(AddressSpaceKind::Memory)
            {
                lower_place_runtime_location_value(ctx, place, result_ty)
            } else if matches!(value_data.repr, mir::ValueRepr::Ptr(_)) {
                if place_yields_location_value(
                    ctx,
                    place,
                    value_data.ty,
                    ctx.body.value_pointer_info(value_id),
                )? {
                    return lower_place_runtime_location_value(ctx, place, result_ty);
                }
                load_place_runtime(ctx, place, value_data.ty, result_ty)
            } else if value_data.repr.address_space().is_some() {
                lower_place_address(ctx, place)
            } else {
                load_place_runtime(
                    ctx,
                    place,
                    value_data.ty,
                    types::value_type(ctx.db, value_data.ty),
                )
            }
        }
        ValueOrigin::ConstRegion(region_id) => {
            let region = ctx.body.const_region(*region_id);
            let gv_ref = ensure_const_data_global(ctx, &region.bytes);
            Ok(ctx
                .fb
                .insert_inst(SymAddr::new(ctx.is, SymbolRef::Global(gv_ref)), Type::I256))
        }
        ValueOrigin::FieldPtr(field_ptr) => {
            let base = lower_value(ctx, field_ptr.base)?;
            if field_ptr.offset_bytes == 0 {
                Ok(base)
            } else if field_ptr.addr_space == AddressSpaceKind::Memory {
                let i8_ptr_ty = ctx.fb.ptr_type(Type::I8);
                let base_ptr = coerce_word_addr_to_ptr(ctx, base, i8_ptr_ty);
                let zero = ctx.fb.make_imm_value(I256::zero());
                let offset = ctx
                    .fb
                    .make_imm_value(I256::from(field_ptr.offset_bytes as u64));
                Ok(ctx.fb.insert_inst(
                    Gep::new(ctx.is, smallvec1::smallvec![base_ptr, zero, offset]),
                    i8_ptr_ty,
                ))
            } else {
                let offset = match field_ptr.addr_space {
                    AddressSpaceKind::Calldata => field_ptr.offset_bytes,
                    AddressSpaceKind::Code => field_ptr.offset_bytes,
                    AddressSpaceKind::Storage | AddressSpaceKind::TransientStorage => {
                        field_ptr.offset_bytes / 32
                    }
                    AddressSpaceKind::Memory => unreachable!(),
                };
                let offset_val = ctx.fb.make_imm_value(I256::from(offset as u64));
                let base = coerce_value_to_word(ctx, base);
                Ok(ctx
                    .fb
                    .insert_inst(Add::new(ctx.is, base, offset_val), Type::I256))
            }
        }
        ValueOrigin::CodeRegionRef(_) => {
            // Code-region refs are zero-sized and should never be used as runtime values.
            // If we reach here, MIR lowering failed to eliminate this usage.
            Err(LowerError::Internal(
                "code-region ref reached codegen as a runtime value".to_string(),
            ))
        }
        ValueOrigin::Expr(_) => {
            // Unlowered expressions shouldn't reach codegen
            Err(LowerError::Internal(
                "unlowered expression in codegen".to_string(),
            ))
        }
    }
}

fn specialized_enum_tag_runtime_ty_for_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    owner_place: &Place<'db>,
) -> Option<Type> {
    let enum_ty = mir::repr::place_object_ref_target_ty(
        ctx.db,
        ctx.core,
        &ctx.body.values,
        &ctx.body.locals,
        owner_place,
    )?;
    enum_ty.as_enum(ctx.db)?;
    let pointer_leaf_infos = mir::repr::pointer_leaf_infos_for_place(
        ctx.db,
        ctx.core,
        &ctx.body.values,
        &ctx.body.locals,
        owner_place,
        enum_ty,
    );
    Some(ctx.runtime_type_for_ty_and_shape(
        enum_ty,
        mir::ir::RuntimeShape::EnumTag { enum_ty },
        &pointer_leaf_infos,
    ))
}

fn move_out_uses_root_local_alias<'db>(
    values: &[mir::ValueData<'db>],
    mut value: mir::ValueId,
) -> bool {
    loop {
        let Some(value_data) = values.get(value.index()) else {
            return false;
        };
        match value_data.origin {
            mir::ValueOrigin::TransparentCast { value: inner } => value = inner,
            mir::ValueOrigin::Local(_) | mir::ValueOrigin::PlaceRoot(_) => return true,
            _ => return false,
        }
    }
}

/// Lower a unary operation.
fn lower_unary_op<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    op: UnOp,
    inner: ValueId,
    result_ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> Result<ValueId, LowerError> {
    let op_ty = types::value_type(db, result_ty);
    let prim = prim_for_runtime_value(db, result_ty);
    let inner = prim
        .map(|prim| coerce_scalar_value(fb, is, inner, op_ty, prim_is_signed(prim)))
        .unwrap_or(inner);
    match op {
        UnOp::Not => {
            let cond = condition_to_i1(fb, inner, is);
            Ok(fb.insert_inst(IsZero::new(is, cond), Type::I1))
        }
        UnOp::Minus => {
            // Arithmetic negation
            let result = fb.insert_inst(Neg::new(is, inner), op_ty);
            Ok(result)
        }
        UnOp::BitNot => {
            // Bitwise not
            let result = fb.insert_inst(Not::new(is, inner), op_ty);
            Ok(result)
        }
        UnOp::Plus => {
            // Unary plus is a no-op
            Ok(inner)
        }
        UnOp::Mut | UnOp::Ref => Ok(inner),
    }
}

/// Lower a binary operation.
fn lower_binary_op<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    op: BinOp,
    lhs: ValueId,
    rhs: ValueId,
    lhs_ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> Result<ValueId, LowerError> {
    match op {
        BinOp::Arith(arith_op) => lower_arith_op(fb, db, arith_op, lhs, rhs, lhs_ty, is),
        BinOp::Comp(comp_op) => lower_comp_op(fb, db, comp_op, lhs, rhs, lhs_ty, is),
        BinOp::Logical(log_op) => lower_logical_op(fb, log_op, lhs, rhs, is),
        BinOp::Index => {
            // Index operations are handled via projections, not as binary ops
            Err(LowerError::Unsupported("index binary op".to_string()))
        }
    }
}

/// Lower an arithmetic binary operation.
fn lower_arith_op<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    op: ArithBinOp,
    lhs: ValueId,
    rhs: ValueId,
    operand_ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> Result<ValueId, LowerError> {
    let operand_ty = mir::repr::word_conversion_leaf_ty(db, operand_ty);
    let op_ty = types::value_type(db, operand_ty);
    let signed = if let TyData::TyBase(TyBase::Prim(prim)) = operand_ty.base_ty(db).data(db) {
        prim_is_signed(*prim)
    } else {
        false
    };
    let lhs = coerce_scalar_value(fb, is, lhs, op_ty, signed);
    let rhs = coerce_scalar_value(fb, is, rhs, op_ty, signed);
    let result = match op {
        ArithBinOp::Add => fb.insert_inst(Add::new(is, lhs, rhs), op_ty),
        ArithBinOp::Sub => fb.insert_inst(Sub::new(is, lhs, rhs), op_ty),
        ArithBinOp::Mul => fb.insert_inst(Mul::new(is, lhs, rhs), op_ty),
        ArithBinOp::Div => {
            if signed {
                fb.insert_evm_sdivo(lhs, rhs)[0]
            } else {
                fb.insert_inst(EvmUdiv::new(is, lhs, rhs), op_ty)
            }
        }
        ArithBinOp::Rem => {
            if signed {
                fb.insert_evm_smodo(lhs, rhs)[0]
            } else {
                fb.insert_inst(EvmUmod::new(is, lhs, rhs), op_ty)
            }
        }
        ArithBinOp::Pow => fb.insert_inst(EvmExp::new(is, lhs, rhs), op_ty),
        // Shl/Shr take (bits, value).
        ArithBinOp::LShift => fb.insert_inst(Shl::new(is, rhs, lhs), op_ty),
        ArithBinOp::RShift => {
            if signed {
                fb.insert_inst(Sar::new(is, rhs, lhs), op_ty)
            } else {
                fb.insert_inst(Shr::new(is, rhs, lhs), op_ty)
            }
        }
        ArithBinOp::BitOr => fb.insert_inst(Or::new(is, lhs, rhs), op_ty),
        ArithBinOp::BitXor => fb.insert_inst(Xor::new(is, lhs, rhs), op_ty),
        ArithBinOp::BitAnd => fb.insert_inst(And::new(is, lhs, rhs), op_ty),
        ArithBinOp::Range => {
            // Range is handled at HIR level, shouldn't reach MIR binary ops
            return Err(LowerError::Unsupported("range operator".to_string()));
        }
    };
    Ok(result)
}

/// Lower a comparison binary operation.
fn lower_comp_op<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    op: CompBinOp,
    lhs: ValueId,
    rhs: ValueId,
    operand_ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> Result<ValueId, LowerError> {
    let operand_ty = mir::repr::word_conversion_leaf_ty(db, operand_ty);
    let signed = if let TyData::TyBase(TyBase::Prim(prim)) = operand_ty.base_ty(db).data(db) {
        prim_is_signed(*prim)
    } else {
        false
    };
    let op_ty = types::value_type(db, operand_ty);
    let lhs = coerce_scalar_value(fb, is, lhs, op_ty, signed);
    let rhs = coerce_scalar_value(fb, is, rhs, op_ty, signed);
    let result = match op {
        CompBinOp::Eq => fb.insert_inst(Eq::new(is, lhs, rhs), Type::I1),
        CompBinOp::NotEq => {
            // neq = iszero(eq(lhs, rhs))
            let eq_result = fb.insert_inst(Eq::new(is, lhs, rhs), Type::I1);
            fb.insert_inst(IsZero::new(is, eq_result), Type::I1)
        }
        CompBinOp::Lt => {
            if signed {
                fb.insert_inst(Slt::new(is, lhs, rhs), Type::I1)
            } else {
                fb.insert_inst(Lt::new(is, lhs, rhs), Type::I1)
            }
        }
        CompBinOp::LtEq => {
            // lhs <= rhs  <==>  !(lhs > rhs)
            let gt_result = if signed {
                fb.insert_inst(Slt::new(is, rhs, lhs), Type::I1)
            } else {
                fb.insert_inst(Gt::new(is, lhs, rhs), Type::I1)
            };
            fb.insert_inst(IsZero::new(is, gt_result), Type::I1)
        }
        CompBinOp::Gt => {
            if signed {
                fb.insert_inst(Slt::new(is, rhs, lhs), Type::I1)
            } else {
                fb.insert_inst(Gt::new(is, lhs, rhs), Type::I1)
            }
        }
        CompBinOp::GtEq => {
            // lhs >= rhs  <==>  !(lhs < rhs)
            let lt_result = if signed {
                fb.insert_inst(Slt::new(is, lhs, rhs), Type::I1)
            } else {
                fb.insert_inst(Lt::new(is, lhs, rhs), Type::I1)
            };
            fb.insert_inst(IsZero::new(is, lt_result), Type::I1)
        }
    };
    Ok(result)
}

/// Lower a logical binary operation.
fn lower_logical_op<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    op: LogicalBinOp,
    lhs: ValueId,
    rhs: ValueId,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> Result<ValueId, LowerError> {
    let result = match op {
        LogicalBinOp::And => fb.insert_inst(And::new(is, lhs, rhs), Type::I1),
        LogicalBinOp::Or => fb.insert_inst(Or::new(is, lhs, rhs), Type::I1),
    };
    Ok(result)
}

/// Lower a MIR intrinsic operation.
fn lower_intrinsic<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    op: IntrinsicOp,
    args: &[mir::ValueId],
) -> Result<Option<ValueId>, LowerError> {
    if matches!(op, IntrinsicOp::CurrentCodeRegionLen) {
        if !args.is_empty() {
            return Err(LowerError::Internal(
                "current_code_region_len requires 0 arguments".to_string(),
            ));
        }
        return Ok(Some(ctx.fb.insert_inst(
            SymSize::new(ctx.is, SymbolRef::CurrentSection),
            Type::I256,
        )));
    }

    if matches!(
        op,
        IntrinsicOp::CodeRegionOffset | IntrinsicOp::CodeRegionLen
    ) {
        let [func_item] = args else {
            return Err(LowerError::Internal(
                "code region intrinsics require 1 argument".to_string(),
            ));
        };
        let value_data = ctx
            .body
            .values
            .get(func_item.index())
            .ok_or_else(|| LowerError::Internal("unknown code region argument".to_string()))?;
        let symbol = match &value_data.origin {
            mir::ValueOrigin::CodeRegionRef(root) => root.symbol.as_deref().ok_or_else(|| {
                LowerError::Unsupported(
                    "code region reference is missing a resolved symbol".to_string(),
                )
            })?,
            _ => {
                return Err(LowerError::Unsupported(
                    "code region intrinsic argument must be a code-region reference".to_string(),
                ));
            }
        };

        let embed_sym = EmbedSymbol::from(symbol.to_string());
        let sym = SymbolRef::Embed(embed_sym);
        return match op {
            IntrinsicOp::CodeRegionOffset => Ok(Some(
                ctx.fb.insert_inst(SymAddr::new(ctx.is, sym), Type::I256),
            )),
            IntrinsicOp::CodeRegionLen => Ok(Some(
                ctx.fb.insert_inst(SymSize::new(ctx.is, sym), Type::I256),
            )),
            _ => unreachable!(),
        };
    }

    // Lower all arguments first
    let mut lowered_args = Vec::with_capacity(args.len());
    for &arg in args {
        let val = lower_value(ctx, arg)?;
        lowered_args.push(val);
    }

    match op {
        IntrinsicOp::AddrOf => {
            let Some(&arg) = lowered_args.first() else {
                return Err(LowerError::Internal(
                    "addr_of requires 1 argument".to_string(),
                ));
            };
            Ok(Some(coerce_value_to_word(ctx, arg)))
        }
        IntrinsicOp::Alloc => {
            let [size] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "alloc requires 1 argument (size)".to_string(),
                ));
            };
            Ok(Some(emit_evm_malloc_word_addr(ctx.fb, *size, ctx.is)))
        }
        IntrinsicOp::Mload => {
            let Some(&addr) = lowered_args.first() else {
                return Err(LowerError::Internal(
                    "mload requires address argument".to_string(),
                ));
            };
            let addr = coerce_value_to_word(ctx, addr);
            Ok(Some(ctx.fb.insert_inst(
                Mload::new(ctx.is, addr, Type::I256),
                Type::I256,
            )))
        }
        IntrinsicOp::Mstore => {
            let [addr, val] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "mstore requires 2 arguments".to_string(),
                ));
            };
            let addr = coerce_value_to_word(ctx, *addr);
            let val = coerce_value_to_word(ctx, *val);
            ctx.fb
                .insert_inst_no_result(Mstore::new(ctx.is, addr, val, Type::I256));
            Ok(None)
        }
        IntrinsicOp::Mstore8 => {
            let [addr, val] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "mstore8 requires 2 arguments".to_string(),
                ));
            };
            let addr = coerce_value_to_word(ctx, *addr);
            let val = coerce_value_to_word(ctx, *val);
            ctx.fb
                .insert_inst_no_result(EvmMstore8::new(ctx.is, addr, val));
            Ok(None)
        }
        IntrinsicOp::Sload => {
            let Some(&key) = lowered_args.first() else {
                return Err(LowerError::Internal(
                    "sload requires 1 argument".to_string(),
                ));
            };
            Ok(Some(
                ctx.fb.insert_inst(EvmSload::new(ctx.is, key), Type::I256),
            ))
        }
        IntrinsicOp::Sstore => {
            let [key, val] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "sstore requires 2 arguments".to_string(),
                ));
            };
            ctx.fb
                .insert_inst_no_result(EvmSstore::new(ctx.is, *key, *val));
            Ok(None)
        }
        IntrinsicOp::Calldataload => {
            let Some(&offset) = lowered_args.first() else {
                return Err(LowerError::Internal(
                    "calldataload requires 1 argument".to_string(),
                ));
            };
            Ok(Some(ctx.fb.insert_inst(
                EvmCalldataLoad::new(ctx.is, offset),
                Type::I256,
            )))
        }
        IntrinsicOp::Calldatasize => Ok(Some(
            ctx.fb.insert_inst(EvmCalldataSize::new(ctx.is), Type::I256),
        )),
        IntrinsicOp::Calldatacopy => {
            let [dst, offset, len] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "calldatacopy requires 3 arguments".to_string(),
                ));
            };
            let dst = coerce_value_to_word(ctx, *dst);
            ctx.fb
                .insert_inst_no_result(EvmCalldataCopy::new(ctx.is, dst, *offset, *len));
            Ok(None)
        }
        IntrinsicOp::Returndatasize => Ok(Some(
            ctx.fb
                .insert_inst(EvmReturnDataSize::new(ctx.is), Type::I256),
        )),
        IntrinsicOp::Returndatacopy => {
            let [dst, offset, len] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "returndatacopy requires 3 arguments".to_string(),
                ));
            };
            let dst = coerce_value_to_word(ctx, *dst);
            ctx.fb
                .insert_inst_no_result(EvmReturnDataCopy::new(ctx.is, dst, *offset, *len));
            Ok(None)
        }
        IntrinsicOp::Codesize => Ok(Some(
            ctx.fb.insert_inst(EvmCodeSize::new(ctx.is), Type::I256),
        )),
        IntrinsicOp::Codecopy => {
            let [dst, offset, len] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "codecopy requires 3 arguments".to_string(),
                ));
            };
            let dst = coerce_value_to_word(ctx, *dst);
            ctx.fb
                .insert_inst_no_result(EvmCodeCopy::new(ctx.is, dst, *offset, *len));
            Ok(None)
        }
        IntrinsicOp::CodeRegionOffset
        | IntrinsicOp::CodeRegionLen
        | IntrinsicOp::CurrentCodeRegionLen => {
            unreachable!("code region intrinsics are handled in the early return above")
        }
        IntrinsicOp::Keccak => {
            let [addr, len] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "keccak requires 2 arguments".to_string(),
                ));
            };
            let addr = coerce_value_to_word(ctx, *addr);
            Ok(Some(ctx.fb.insert_inst(
                EvmKeccak256::new(ctx.is, addr, *len),
                Type::I256,
            )))
        }
        IntrinsicOp::Addmod => {
            let [a, b, m] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "addmod requires 3 arguments".to_string(),
                ));
            };
            Ok(Some(ctx.fb.insert_inst(
                EvmAddMod::new(ctx.is, *a, *b, *m),
                Type::I256,
            )))
        }
        IntrinsicOp::Mulmod => {
            let [a, b, m] = lowered_args.as_slice() else {
                return Err(LowerError::Internal(
                    "mulmod requires 3 arguments".to_string(),
                ));
            };
            Ok(Some(ctx.fb.insert_inst(
                EvmMulMod::new(ctx.is, *a, *b, *m),
                Type::I256,
            )))
        }
        IntrinsicOp::Caller => Ok(Some(ctx.fb.insert_inst(EvmCaller::new(ctx.is), Type::I256))),
        IntrinsicOp::Callvalue => Ok(Some(
            ctx.fb.insert_inst(EvmCallValue::new(ctx.is), Type::I256),
        )),
        IntrinsicOp::ReturnData | IntrinsicOp::Revert => Err(LowerError::Internal(
            "terminating intrinsic must be lowered as Terminator::TerminatingCall".to_string(),
        )),
    }
}

/// Convert a BigUint to I256.
fn biguint_to_i256(n: &BigUint) -> I256 {
    // Convert to bytes and then to I256
    let bytes = n.to_bytes_be();
    if bytes.is_empty() {
        return I256::zero();
    }
    // Pad to 32 bytes (right-aligned for big-endian)
    let mut padded = [0u8; 32];
    let start = 32usize.saturating_sub(bytes.len());
    let copy_len = bytes.len().min(32);
    padded[start..start + copy_len].copy_from_slice(&bytes[bytes.len() - copy_len..]);
    I256::from_be_bytes(&padded)
}

/// Convert bytes to I256.
///
/// Matches Yul's `0x...` literal semantics by interpreting the bytes as a big-endian integer.
fn bytes_to_i256(bytes: &[u8]) -> I256 {
    let mut padded = [0u8; 32];
    let copy_len = bytes.len().min(32);
    let start = 32 - copy_len;
    padded[start..start + copy_len].copy_from_slice(&bytes[bytes.len() - copy_len..]);
    I256::from_be_bytes(&padded)
}

/// Returns the Sonatina Type for a Fe primitive type, or None if not a sub-word type.
fn prim_to_sonatina_type(prim: PrimTy) -> Option<Type> {
    types::prim_scalar_type(prim).filter(|ty| *ty != Type::I256)
}

/// Returns true if the primitive type is signed.
fn prim_is_signed(prim: PrimTy) -> bool {
    matches!(
        prim,
        PrimTy::I8
            | PrimTy::I16
            | PrimTy::I32
            | PrimTy::I64
            | PrimTy::I128
            | PrimTy::I256
            | PrimTy::Isize
    )
}

fn int_type_bits(ty: Type) -> Option<u16> {
    match ty {
        Type::I1 => Some(1),
        Type::I8 => Some(8),
        Type::I16 => Some(16),
        Type::I32 => Some(32),
        Type::I64 => Some(64),
        Type::I128 => Some(128),
        Type::I256 => Some(256),
        _ => None,
    }
}

fn cast_int_value<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
    value: ValueId,
    target_ty: Type,
    signed: bool,
) -> ValueId {
    let current_ty = fb.type_of(value);
    if current_ty == target_ty {
        return value;
    }

    let Some(current_bits) = int_type_bits(current_ty) else {
        return value;
    };
    let Some(target_bits) = int_type_bits(target_ty) else {
        return value;
    };

    if current_bits > target_bits {
        fb.insert_inst(Trunc::new(is, value, target_ty), target_ty)
    } else if current_bits < target_bits {
        if signed && current_ty != Type::I1 {
            fb.insert_inst(Sext::new(is, value, target_ty), target_ty)
        } else {
            fb.insert_inst(Zext::new(is, value, target_ty), target_ty)
        }
    } else {
        value
    }
}

fn prim_for_runtime_value<'db>(
    db: &'db DriverDataBase,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Option<PrimTy> {
    let ty = match ty.as_capability(db) {
        Some((CapabilityKind::View, inner)) => inner,
        _ => ty,
    };
    let ty = mir::repr::word_conversion_leaf_ty(db, ty);
    let TyData::TyBase(TyBase::Prim(prim)) = ty.base_ty(db).data(db) else {
        return None;
    };
    Some(*prim)
}

fn coerce_scalar_value<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
    value: ValueId,
    target_ty: Type,
    signed: bool,
) -> ValueId {
    if target_ty == Type::I1 {
        condition_to_i1(fb, value, is)
    } else {
        cast_int_value(fb, is, value, target_ty, signed)
    }
}

fn coerce_runtime_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    value: ValueId,
    value_ty: hir::analysis::ty::ty_def::TyId<'db>,
    target_ty: Type,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let current_ty = fb.type_of(value);
    if current_ty == target_ty {
        return value;
    }
    if target_ty == Type::Unit {
        return types::zero_value(fb, Type::Unit);
    }
    if current_ty == Type::Unit {
        return types::zero_value(fb, target_ty);
    }

    match prim_for_runtime_value(db, value_ty) {
        Some(PrimTy::Bool) => coerce_scalar_value(fb, is, value, target_ty, false),
        Some(prim) => coerce_scalar_value(fb, is, value, target_ty, prim_is_signed(prim)),
        None => cast_int_value(fb, is, value, target_ty, false),
    }
}

fn make_int_immediate<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    value: I256,
    ty: Type,
) -> ValueId {
    fb.make_imm_value(Immediate::from_i256(value, ty))
}

fn extract_evm_byte<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
    pos: u64,
    value: ValueId,
) -> ValueId {
    let pos = fb.make_imm_value(I256::from(pos));
    let ty = fb.type_of(value);
    fb.insert_inst(EvmByte::new(is, pos, value), ty)
}

/// Applies `from_word` conversion after loading a value.
///
/// This mirrors the stdlib `WordRepr::from_word` semantics, but returns the
/// loaded value at its natural Sonatina type.
fn apply_from_word<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    raw_value: ValueId,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ty = mir::repr::word_conversion_leaf_ty(db, ty);
    let base_ty = ty.base_ty(db);

    if let TyData::TyBase(TyBase::Prim(prim)) = base_ty.data(db) {
        match prim {
            PrimTy::Bool => condition_to_i1(fb, raw_value, is),
            _ => prim_to_sonatina_type(*prim)
                .map(|small_ty| cast_int_value(fb, is, raw_value, small_ty, prim_is_signed(*prim)))
                .unwrap_or(raw_value),
        }
    } else {
        // Non-primitive type, no conversion
        raw_value
    }
}

/// Applies `to_word` conversion before storing a value.
///
/// This mirrors the stdlib `WordRepr::to_word` semantics, converting a natural-width
/// Sonatina integer back into an EVM word.
fn apply_to_word<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    db: &'db DriverDataBase,
    value: ValueId,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ty = mir::repr::word_conversion_leaf_ty(db, ty);
    let base_ty = ty.base_ty(db);

    if let TyData::TyBase(TyBase::Prim(prim)) = base_ty.data(db) {
        match prim {
            PrimTy::Bool => {
                let bool_val = condition_to_i1(fb, value, is);
                fb.insert_inst(Zext::new(is, bool_val, Type::I256), Type::I256)
            }
            _ => prim_to_sonatina_type(*prim)
                .map(|small_ty| {
                    let cast = cast_int_value(fb, is, value, small_ty, prim_is_signed(*prim));
                    if prim_is_signed(*prim) {
                        fb.insert_inst(Sext::new(is, cast, Type::I256), Type::I256)
                    } else {
                        fb.insert_inst(Zext::new(is, cast, Type::I256), Type::I256)
                    }
                })
                .unwrap_or(value),
        }
    } else {
        // Non-primitive type, no conversion
        value
    }
}

/// Maps a Fe type to a sonatina struct/array type for GEP-based addressing.
///
/// Returns `Some(Type)` for types that can be represented as sonatina compound types
/// (structs, tuples, arrays of such). Returns `None` for types where we should fall
/// back to manual offset arithmetic (enums, zero-sized types, plain scalars).
///
/// Uses a cache to avoid creating duplicate compound type definitions.
///
/// The cache key is structural for tuples/arrays and nominal for ADTs so object-backed
/// call boundaries can reuse a single Sonatina compound type even when Fe produces
/// distinct but equivalent aggregate `TyId`s.
fn normalize_sonatina_type_input<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> hir::analysis::ty::ty_def::TyId<'db> {
    normalize_ty(db, ty, core.scope, PredicateListId::empty_list(db))
}

fn normalize_pointer_leaf_infos<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
    mir::repr::normalize_pointer_leaf_infos(pointer_leaf_infos.to_vec())
}

fn projection_strip_prefix<'db>(
    path: &mir::MirProjectionPath<'db>,
    prefix: &mir::MirProjectionPath<'db>,
) -> Option<mir::MirProjectionPath<'db>> {
    if !prefix.is_prefix_of(path) {
        return None;
    }

    let mut suffix = mir::MirProjectionPath::new();
    for proj in path.iter().skip(prefix.len()) {
        suffix.push(proj.clone());
    }
    Some(suffix)
}

fn root_pointer_leaf_info<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
) -> Option<PointerInfo<'db>> {
    let root_infos: Vec<_> = pointer_leaf_infos
        .iter()
        .filter(|(path, _)| path.is_empty())
        .cloned()
        .collect();
    normalize_pointer_leaf_infos(&root_infos)
        .into_iter()
        .next()
        .map(|(_, info)| info)
}

fn strip_pointer_leaf_info_prefix<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    prefix: &mir::MirProjectionPath<'db>,
) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
    normalize_pointer_leaf_infos(
        &pointer_leaf_infos
            .iter()
            .filter_map(|(path, info)| {
                projection_strip_prefix(path, prefix).map(|suffix| (suffix, *info))
            })
            .collect::<Vec<_>>(),
    )
}

fn field_pointer_leaf_infos<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    field_idx: usize,
) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
    strip_pointer_leaf_info_prefix(
        pointer_leaf_infos,
        &mir::MirProjectionPath::from_projection(Projection::Field(field_idx)),
    )
}

fn array_elem_pointer_leaf_infos<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
    let mut elem_pointer_leaf_infos = Vec::new();
    for (path, info) in pointer_leaf_infos {
        let Some(first_proj) = path.iter().next() else {
            continue;
        };
        if !matches!(first_proj, Projection::Index(_)) {
            continue;
        }
        let mut suffix = mir::MirProjectionPath::new();
        for proj in path.iter().skip(1) {
            suffix.push(proj.clone());
        }
        elem_pointer_leaf_infos.push((suffix, *info));
    }
    normalize_pointer_leaf_infos(&elem_pointer_leaf_infos)
}

fn variant_field_pointer_leaf_infos<'db>(
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    variant: hir::hir_def::EnumVariant<'db>,
    enum_ty: hir::analysis::ty::ty_def::TyId<'db>,
    field_idx: usize,
) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
    strip_pointer_leaf_info_prefix(
        pointer_leaf_infos,
        &mir::MirProjectionPath::from_projection(Projection::VariantField {
            variant,
            enum_ty,
            field_idx,
        }),
    )
}

fn sonatina_pointer_pointee_cache_key(inner_key: String) -> String {
    if inner_key == "unit" || inner_key.starts_with("none:") {
        "ptr<i8>".to_string()
    } else {
        format!("ptr<{inner_key}>")
    }
}

fn sonatina_object_ref_target_cache_key<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    target_layout: &TargetDataLayout,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> String {
    let target_key = fe_ty_to_sonatina_effective_cache_key(db, core, target_layout, ty, &[], true);
    if !target_key.starts_with("none:") {
        return target_key;
    }

    let size = layout::ty_memory_size_or_word_in(db, target_layout, ty)
        .expect("object-backed runtime types must have a known memory size");
    format!("array[{:?};{size}]", Type::I8)
}

fn sonatina_scalar_cache_key<'db>(
    db: &'db DriverDataBase,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> String {
    format!("{:?}", types::value_type(db, ty))
}

fn fe_ty_to_sonatina_effective_cache_key<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    target_layout: &TargetDataLayout,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    object_layout: bool,
) -> String {
    let mut ty = normalize_sonatina_type_input(db, core, ty);
    if object_layout {
        ty = mir::repr::object_layout_ty(db, core, ty);
    }

    if is_erased_runtime_ty(db, target_layout, ty) {
        return "unit".to_string();
    }

    let root_pointer_info = root_pointer_leaf_info(pointer_leaf_infos);
    if let Some((capability, inner)) = ty.as_capability(db) {
        return match capability {
            CapabilityKind::View => fe_ty_to_sonatina_effective_cache_key(
                db,
                core,
                target_layout,
                inner,
                pointer_leaf_infos,
                object_layout,
            ),
            CapabilityKind::Mut | CapabilityKind::Ref
                if root_pointer_info
                    .is_some_and(|info| info.address_space != AddressSpaceKind::Memory) =>
            {
                format!("{:?}", Type::I256)
            }
            CapabilityKind::Mut | CapabilityKind::Ref
                if root_pointer_info
                    .is_some_and(|info| info.address_space == AddressSpaceKind::Memory)
                    && scalar_handle_object_ref_target_ty(db, core, inner).is_some() =>
            {
                format!(
                    "objref<{}>",
                    sonatina_object_ref_target_cache_key(db, core, target_layout, inner)
                )
            }
            CapabilityKind::Mut | CapabilityKind::Ref
                if object_layout && object_field_uses_object_ref(db, core, inner) =>
            {
                format!(
                    "objref<{}>",
                    sonatina_object_ref_target_cache_key(db, core, target_layout, inner)
                )
            }
            CapabilityKind::Mut => sonatina_pointer_pointee_cache_key(
                fe_ty_to_sonatina_effective_cache_key(db, core, target_layout, inner, &[], false),
            ),
            CapabilityKind::Ref if lowers_by_ref_layout(db, core, inner) => {
                sonatina_pointer_pointee_cache_key(fe_ty_to_sonatina_effective_cache_key(
                    db,
                    core,
                    target_layout,
                    inner,
                    &[],
                    false,
                ))
            }
            CapabilityKind::Ref => format!("{:?}", Type::I256),
        };
    }

    if let Some(target_ty) = memory_effect_pointer_target_ty(db, core, ty) {
        return sonatina_pointer_pointee_cache_key(fe_ty_to_sonatina_effective_cache_key(
            db,
            core,
            target_layout,
            target_ty,
            &[],
            false,
        ));
    }

    if let Some(inner) = mir::repr::transparent_newtype_field_ty(db, ty) {
        return fe_ty_to_sonatina_effective_cache_key(
            db,
            core,
            target_layout,
            inner,
            pointer_leaf_infos,
            object_layout,
        );
    }

    if matches!(
        mir::repr::repr_kind_for_ty(db, core, ty),
        mir::repr::ReprKind::Word
    ) {
        return sonatina_scalar_cache_key(db, ty);
    }

    let prefix = if object_layout { "obj:" } else { "" };
    match ty.base_ty(db).data(db) {
        TyData::TyBase(TyBase::Prim(PrimTy::String)) => {
            format!("none:string:{prefix}{}", ty.pretty_print(db))
        }
        TyData::TyBase(TyBase::Prim(PrimTy::Tuple(_))) => {
            let field_tys = ty.field_types(db);
            if field_tys.is_empty() {
                return "unit".to_string();
            }
            let field_keys = field_tys
                .iter()
                .enumerate()
                .map(|(field_idx, field_ty)| {
                    fe_ty_to_sonatina_effective_cache_key(
                        db,
                        core,
                        target_layout,
                        *field_ty,
                        &field_pointer_leaf_infos(pointer_leaf_infos, field_idx),
                        object_layout,
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!("{prefix}tuple({field_keys})")
        }
        TyData::TyBase(TyBase::Prim(PrimTy::Array)) => {
            let elem_ty =
                layout::array_elem_ty(db, ty).expect("array lowering should have an element type");
            let len = layout::array_len(db, ty).expect("array lowering should have a length");
            let elem_key = fe_ty_to_sonatina_effective_cache_key(
                db,
                core,
                target_layout,
                elem_ty,
                &array_elem_pointer_leaf_infos(pointer_leaf_infos),
                object_layout,
            );
            format!("{prefix}array[{elem_key};{len}]")
        }
        TyData::TyBase(TyBase::Adt(adt_def)) => match adt_def.adt_ref(db) {
            AdtRef::Struct(_) => {
                let field_keys = ty
                    .field_types(db)
                    .iter()
                    .enumerate()
                    .map(|(field_idx, field_ty)| {
                        fe_ty_to_sonatina_effective_cache_key(
                            db,
                            core,
                            target_layout,
                            *field_ty,
                            &field_pointer_leaf_infos(pointer_leaf_infos, field_idx),
                            object_layout,
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(",");
                format!("{prefix}adt:{adt_def:?}{{{field_keys}}}")
            }
            AdtRef::Enum(enum_) => {
                let variant_keys = (0..enum_.len_variants(db))
                    .map(|idx| {
                        let variant = hir::hir_def::EnumVariant::new(enum_, idx);
                        let ctor = ConstructorKind::Variant(variant, ty);
                        let fields = ctor
                            .field_types(db)
                            .iter()
                            .enumerate()
                            .map(|(field_idx, field_ty)| {
                                fe_ty_to_sonatina_effective_cache_key(
                                    db,
                                    core,
                                    target_layout,
                                    *field_ty,
                                    &variant_field_pointer_leaf_infos(
                                        pointer_leaf_infos,
                                        variant,
                                        ty,
                                        field_idx,
                                    ),
                                    object_layout,
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(",");
                        format!("{variant:?}({fields})")
                    })
                    .collect::<Vec<_>>()
                    .join("|");
                format!("{prefix}adt:{adt_def:?}[{variant_keys}]")
            }
        },
        TyData::TyBase(TyBase::Contract(_)) | TyData::TyBase(TyBase::Func(_)) => "unit".to_string(),
        _ => sonatina_scalar_cache_key(db, ty),
    }
}

fn fe_ty_to_sonatina_cache_key<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    target_layout: &TargetDataLayout,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
) -> String {
    fe_ty_to_sonatina_effective_cache_key(db, core, target_layout, ty, pointer_leaf_infos, false)
}

fn fe_object_ty_to_sonatina_cache_key<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    target_layout: &TargetDataLayout,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
    pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
) -> String {
    fe_ty_to_sonatina_effective_cache_key(db, core, target_layout, ty, pointer_leaf_infos, true)
}

fn memory_effect_pointer_target_ty<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Option<TyId<'db>> {
    (mir::repr::effect_provider_space_for_ty(db, core, ty) == Some(AddressSpaceKind::Memory))
        .then(|| mir::repr::effect_provider_target_ty(db, core, ty))
        .flatten()
}

fn lowers_by_ref_layout<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    mut ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> bool {
    loop {
        if let Some((capability, inner)) = ty.as_capability(db) {
            if matches!(capability, CapabilityKind::View) {
                ty = inner;
                continue;
            }
            return false;
        }

        if memory_effect_pointer_target_ty(db, core, ty).is_some() {
            return false;
        }

        if let Some(inner) = mir::repr::transparent_newtype_field_ty(db, ty) {
            ty = inner;
            continue;
        }

        return ty.is_array(db)
            || ty.is_tuple(db)
            || ty
                .adt_ref(db)
                .is_some_and(|adt| matches!(adt, AdtRef::Struct(_) | AdtRef::Enum(_)));
    }
}

fn scalar_handle_object_ref_target_ty<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Option<TyId<'db>> {
    mir::repr::memory_scalar_object_ref_target_ty(db, core, ty)
}

fn object_field_uses_object_ref<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> bool {
    if !mir::repr::supports_object_ref_runtime_ty(db, core, ty) {
        return false;
    }

    if matches!(
        mir::repr::repr_kind_for_ty(db, core, ty),
        mir::repr::ReprKind::Ref
    ) {
        return true;
    }

    let object_ty = mir::repr::object_layout_ty(db, core, ty);
    object_ty != ty
        && matches!(
            mir::repr::repr_kind_for_ty(db, core, object_ty),
            mir::repr::ReprKind::Ref
        )
}

fn const_aggregate_object_copy_compatible<'db>(
    db: &'db DriverDataBase,
    core: &mir::CoreLib<'db>,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> bool {
    let ty = mir::repr::object_layout_ty(db, core, ty);

    if layout::is_zero_sized_ty(db, ty) {
        return true;
    }

    if let Some((CapabilityKind::View, inner)) = ty.as_capability(db) {
        return const_aggregate_object_copy_compatible(db, core, inner);
    }

    if let Some(inner) = mir::repr::transparent_newtype_field_ty(db, ty) {
        return const_aggregate_object_copy_compatible(db, core, inner);
    }

    match mir::repr::repr_kind_for_ty(db, core, ty) {
        mir::repr::ReprKind::Zst | mir::repr::ReprKind::Word => true,
        mir::repr::ReprKind::Ptr(_) => false,
        mir::repr::ReprKind::Ref => {
            if ty.is_array(db) {
                return layout::array_elem_ty(db, ty).is_some_and(|elem_ty| {
                    const_aggregate_object_copy_compatible(db, core, elem_ty)
                });
            }

            if ty.is_tuple(db)
                || ty
                    .adt_ref(db)
                    .is_some_and(|adt| matches!(adt, AdtRef::Struct(_)))
            {
                return ty
                    .field_types(db)
                    .iter()
                    .copied()
                    .all(|field_ty| const_aggregate_object_copy_compatible(db, core, field_ty));
            }

            false
        }
    }
}

impl<'db> TypeLowerer<'_, 'db> {
    pub(super) fn fe_ty_to_sonatina_with_pointer_leaf_infos(
        &mut self,
        ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Type> {
        let cache_key = fe_ty_to_sonatina_cache_key(
            self.db,
            self.core,
            self.target_layout,
            ty,
            pointer_leaf_infos,
        );
        if let Some(cached) = self.cache.get(&cache_key) {
            return *cached;
        }

        let result = self.fe_ty_to_sonatina_inner(ty, pointer_leaf_infos);
        self.cache.insert(cache_key, result);
        result
    }

    pub(super) fn fe_object_ty_to_sonatina_with_pointer_leaf_infos(
        &mut self,
        ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Type> {
        let cache_key = fe_object_ty_to_sonatina_cache_key(
            self.db,
            self.core,
            self.target_layout,
            ty,
            pointer_leaf_infos,
        );
        if let Some(cached) = self.cache.get(&cache_key) {
            return *cached;
        }

        let result = self.fe_object_ty_to_sonatina_inner(ty, pointer_leaf_infos);
        self.cache.insert(cache_key, result);
        result
    }

    pub(super) fn fe_ty_to_sonatina(&mut self, ty: TyId<'db>) -> Option<Type> {
        self.fe_ty_to_sonatina_with_pointer_leaf_infos(ty, &[])
    }

    pub(super) fn runtime_type_for_ty_and_shape(
        &mut self,
        ty: TyId<'db>,
        shape: mir::ir::RuntimeShape<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Type {
        match shape {
            mir::ir::RuntimeShape::Unresolved => {
                panic!("unresolved MIR runtime shape reached Sonatina codegen")
            }
            mir::ir::RuntimeShape::Erased => Type::Unit,
            mir::ir::RuntimeShape::EnumTag { enum_ty } => {
                self.runtime_enum_tag_type_from_target(enum_ty, pointer_leaf_infos)
            }
            mir::ir::RuntimeShape::ObjectRef { target_ty } => {
                self.runtime_object_ref_type_from_target(ty, target_ty, pointer_leaf_infos)
            }
            mir::ir::RuntimeShape::Word(kind) => types::runtime_word_type(kind),
            mir::ir::RuntimeShape::MemoryPtr { target_ty } => target_ty
                .map(|target_ty| {
                    self.runtime_pointer_type_from_target(ty, target_ty, pointer_leaf_infos)
                })
                .unwrap_or_else(|| self.builder.ptr_type(Type::I8)),
            mir::ir::RuntimeShape::AddressWord(_) => Type::I256,
        }
    }

    fn pointer_like_sonatina_ty(
        &mut self,
        ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Type {
        let pointee = self
            .fe_ty_to_sonatina_with_pointer_leaf_infos(ty, pointer_leaf_infos)
            .unwrap_or(Type::I8);
        self.builder.ptr_type(if pointee == Type::Unit {
            Type::I8
        } else {
            pointee
        })
    }

    fn scalar_handle_sonatina_ty(&mut self, ty: TyId<'db>) -> Option<Type> {
        let target_ty = self
            .fe_object_ty_to_sonatina_with_pointer_leaf_infos(ty, &[])
            .or_else(|| {
                let size = layout::ty_memory_size_or_word_in(self.db, self.target_layout, ty)?;
                Some(self.builder.declare_array_type(Type::I8, size))
            })?;
        Some(self.builder.objref_type(target_ty))
    }

    fn runtime_target_pointer_leaf_infos(
        &self,
        owner_ty: TyId<'db>,
        target_ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Vec<(mir::MirProjectionPath<'db>, PointerInfo<'db>)> {
        if let Some((_, inner)) = owner_ty.as_capability(self.db) {
            let nested_pointer_leaf_infos: Vec<_> = pointer_leaf_infos
                .iter()
                .filter(|(path, _)| !path.is_empty())
                .cloned()
                .collect();
            return self.runtime_target_pointer_leaf_infos(
                inner,
                target_ty,
                &nested_pointer_leaf_infos,
            );
        }

        if mir::repr::effect_provider_space_for_ty(self.db, self.core, owner_ty).is_some() {
            return Vec::new();
        }

        if let Some(inner) = mir::repr::transparent_newtype_field_ty(self.db, owner_ty) {
            return self.runtime_target_pointer_leaf_infos(inner, target_ty, pointer_leaf_infos);
        }

        if owner_ty == target_ty
            || mir::repr::object_layout_ty(self.db, self.core, owner_ty) == target_ty
        {
            return pointer_leaf_infos.to_vec();
        }

        Vec::new()
    }

    fn runtime_pointer_type_from_target(
        &mut self,
        owner_ty: TyId<'db>,
        target_ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Type {
        let pointee_leaf_infos =
            self.runtime_target_pointer_leaf_infos(owner_ty, target_ty, pointer_leaf_infos);
        let pointee = self
            .fe_ty_to_sonatina_with_pointer_leaf_infos(target_ty, &pointee_leaf_infos)
            .unwrap_or(Type::I8);
        if pointee == Type::Unit {
            return self.builder.ptr_type(Type::I8);
        }
        self.builder.ptr_type(pointee)
    }

    fn runtime_object_ref_type_from_target(
        &mut self,
        owner_ty: TyId<'db>,
        target_ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Type {
        let object_pointer_leaf_infos =
            self.runtime_target_pointer_leaf_infos(owner_ty, target_ty, pointer_leaf_infos);
        let object_ty = self
            .fe_object_ty_to_sonatina_with_pointer_leaf_infos(target_ty, &object_pointer_leaf_infos)
            .unwrap_or_else(|| {
                let size =
                    layout::ty_memory_size_or_word_in(self.db, self.target_layout, target_ty)
                        .expect("object-backed runtime types must have a known memory size");
                self.builder.declare_array_type(Type::I8, size)
            });
        self.builder.objref_type(object_ty)
    }

    fn runtime_enum_tag_type_from_target(
        &mut self,
        enum_ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Type {
        let enum_ty = self
            .fe_object_ty_to_sonatina_with_pointer_leaf_infos(enum_ty, pointer_leaf_infos)
            .expect("enum-tag runtime shapes must lower to a Sonatina enum type");
        let Type::Compound(enum_ty) = enum_ty else {
            panic!("enum-tag runtime shapes must lower to a Sonatina compound enum type");
        };
        Type::EnumTag(enum_ty)
    }

    fn variant_data(
        &mut self,
        enum_ty: TyId<'db>,
        object_layout: bool,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Vec<VariantData>> {
        let enum_ = enum_ty.as_enum(self.db)?;
        let mut variants = Vec::with_capacity(enum_.len_variants(self.db));
        for idx in 0..enum_.len_variants(self.db) {
            let variant = hir::hir_def::EnumVariant::new(enum_, idx);
            let ctor = ConstructorKind::Variant(variant, enum_ty);
            let mut fields = Vec::with_capacity(ctor.field_types(self.db).len());
            for (field_idx, field_ty) in ctor.field_types(self.db).iter().copied().enumerate() {
                let field_pointer_leaf_infos = variant_field_pointer_leaf_infos(
                    pointer_leaf_infos,
                    variant,
                    enum_ty,
                    field_idx,
                );
                let lowered = if object_layout {
                    self.fe_object_ty_to_sonatina_with_pointer_leaf_infos(
                        field_ty,
                        &field_pointer_leaf_infos,
                    )
                } else {
                    self.fe_ty_to_sonatina_with_pointer_leaf_infos(
                        field_ty,
                        &field_pointer_leaf_infos,
                    )
                }?;
                fields.push(lowered);
            }
            variants.push(VariantData {
                name: variant.name(self.db).unwrap_or("anon").to_string(),
                explicit_discriminant: Some(idx as u128),
                fields,
            });
        }
        Some(variants)
    }

    fn declare_enum_type(
        &mut self,
        enum_ty: TyId<'db>,
        object_layout: bool,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Type> {
        let variants = self.variant_data(enum_ty, object_layout, pointer_leaf_infos)?;
        let name = enum_ty
            .adt_ref(self.db)
            .and_then(|adt_ref| adt_ref.name(self.db))
            .map(|id| id.data(self.db).to_string())
            .unwrap_or_else(|| "anon".to_string());
        let id = *self.name_counter;
        *self.name_counter += 1;
        let prefix = if object_layout { "__fe_obj" } else { "__fe" };
        Some(self.builder.declare_enum_type(
            &format!("{prefix}_{name}_{id}"),
            &variants,
            EnumReprHint::Default,
        ))
    }

    fn fe_ty_to_sonatina_inner(
        &mut self,
        ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Type> {
        let ty = normalize_sonatina_type_input(self.db, self.core, ty);
        if is_erased_runtime_ty(self.db, self.target_layout, ty) {
            return Some(Type::Unit);
        }

        let root_pointer_info = root_pointer_leaf_info(pointer_leaf_infos);
        if let Some((capability, inner)) = ty.as_capability(self.db) {
            return match capability {
                CapabilityKind::View => {
                    self.fe_ty_to_sonatina_with_pointer_leaf_infos(inner, pointer_leaf_infos)
                }
                CapabilityKind::Mut | CapabilityKind::Ref
                    if root_pointer_info
                        .is_some_and(|info| info.address_space != AddressSpaceKind::Memory) =>
                {
                    Some(Type::I256)
                }
                CapabilityKind::Mut | CapabilityKind::Ref
                    if root_pointer_info
                        .is_some_and(|info| info.address_space == AddressSpaceKind::Memory)
                        && scalar_handle_object_ref_target_ty(self.db, self.core, inner)
                            .is_some() =>
                {
                    self.scalar_handle_sonatina_ty(inner)
                }
                CapabilityKind::Mut => Some(self.pointer_like_sonatina_ty(inner, &[])),
                CapabilityKind::Ref if lowers_by_ref_layout(self.db, self.core, inner) => {
                    Some(self.pointer_like_sonatina_ty(inner, &[]))
                }
                CapabilityKind::Ref => Some(Type::I256),
            };
        }

        if let Some(target_ty) = memory_effect_pointer_target_ty(self.db, self.core, ty) {
            return Some(self.pointer_like_sonatina_ty(target_ty, &[]));
        }

        if let Some(inner) = mir::repr::transparent_newtype_field_ty(self.db, ty) {
            return self.fe_ty_to_sonatina_with_pointer_leaf_infos(inner, pointer_leaf_infos);
        }

        if matches!(
            mir::repr::repr_kind_for_ty(self.db, self.core, ty),
            mir::repr::ReprKind::Word
        ) {
            return Some(types::value_type(self.db, ty));
        }

        let base_ty = ty.base_ty(self.db);
        match base_ty.data(self.db) {
            TyData::TyBase(TyBase::Prim(prim)) => match prim {
                PrimTy::String => None,
                PrimTy::Tuple(_) => {
                    let field_tys = ty.field_types(self.db);
                    if field_tys.is_empty() {
                        return Some(Type::Unit);
                    }
                    let mut sonatina_fields = Vec::with_capacity(field_tys.len());
                    for (field_idx, field_ty) in field_tys.iter().copied().enumerate() {
                        let field_pointer_leaf_infos =
                            field_pointer_leaf_infos(pointer_leaf_infos, field_idx);
                        sonatina_fields.push(self.fe_ty_to_sonatina_with_pointer_leaf_infos(
                            field_ty,
                            &field_pointer_leaf_infos,
                        )?);
                    }
                    let id = *self.name_counter;
                    *self.name_counter += 1;
                    Some(self.builder.declare_struct_type(
                        &format!("__fe_tuple_{id}"),
                        &sonatina_fields,
                        false,
                    ))
                }
                PrimTy::Array => {
                    let elem_ty = layout::array_elem_ty(self.db, ty)?;
                    let len = layout::array_len(self.db, ty)?;
                    let elem_pointer_leaf_infos = array_elem_pointer_leaf_infos(pointer_leaf_infos);
                    let sonatina_elem = self.fe_ty_to_sonatina_with_pointer_leaf_infos(
                        elem_ty,
                        &elem_pointer_leaf_infos,
                    )?;
                    Some(self.builder.declare_array_type(sonatina_elem, len))
                }
                _ => Some(types::value_type(self.db, ty)),
            },
            TyData::TyBase(TyBase::Adt(adt_def)) => match adt_def.adt_ref(self.db) {
                AdtRef::Struct(_) => {
                    let field_tys = ty.field_types(self.db);
                    let mut sonatina_fields = Vec::with_capacity(field_tys.len());
                    for (field_idx, field_ty) in field_tys.iter().copied().enumerate() {
                        let field_pointer_leaf_infos =
                            field_pointer_leaf_infos(pointer_leaf_infos, field_idx);
                        sonatina_fields.push(self.fe_ty_to_sonatina_with_pointer_leaf_infos(
                            field_ty,
                            &field_pointer_leaf_infos,
                        )?);
                    }
                    let name = adt_def
                        .adt_ref(self.db)
                        .name(self.db)
                        .map(|id| id.data(self.db).to_string())
                        .unwrap_or_else(|| "anon".to_string());
                    let id = *self.name_counter;
                    *self.name_counter += 1;
                    Some(self.builder.declare_struct_type(
                        &format!("__fe_{name}_{id}"),
                        &sonatina_fields,
                        false,
                    ))
                }
                AdtRef::Enum(_) => self.declare_enum_type(ty, false, pointer_leaf_infos),
            },
            TyData::TyBase(TyBase::Contract(_)) | TyData::TyBase(TyBase::Func(_)) => {
                Some(Type::Unit)
            }
            _ => None,
        }
    }

    fn fe_object_ty_to_sonatina_inner(
        &mut self,
        ty: TyId<'db>,
        pointer_leaf_infos: &[(mir::MirProjectionPath<'db>, PointerInfo<'db>)],
    ) -> Option<Type> {
        let ty = normalize_sonatina_type_input(
            self.db,
            self.core,
            mir::repr::object_layout_ty(self.db, self.core, ty),
        );
        if is_erased_runtime_ty(self.db, self.target_layout, ty) {
            return Some(Type::Unit);
        }

        let root_pointer_info = root_pointer_leaf_info(pointer_leaf_infos);
        if let Some((capability, inner)) = ty.as_capability(self.db) {
            return match capability {
                CapabilityKind::View => {
                    self.fe_object_ty_to_sonatina_with_pointer_leaf_infos(inner, pointer_leaf_infos)
                }
                CapabilityKind::Mut | CapabilityKind::Ref
                    if root_pointer_info
                        .is_some_and(|info| info.address_space != AddressSpaceKind::Memory) =>
                {
                    Some(Type::I256)
                }
                CapabilityKind::Mut | CapabilityKind::Ref
                    if root_pointer_info
                        .is_some_and(|info| info.address_space == AddressSpaceKind::Memory)
                        && scalar_handle_object_ref_target_ty(self.db, self.core, inner)
                            .is_some() =>
                {
                    self.scalar_handle_sonatina_ty(inner)
                }
                CapabilityKind::Mut | CapabilityKind::Ref
                    if object_field_uses_object_ref(self.db, self.core, inner) =>
                {
                    let target_ty = self
                        .fe_object_ty_to_sonatina_with_pointer_leaf_infos(inner, &[])
                        .or_else(|| {
                            let size = layout::ty_memory_size_or_word_in(
                                self.db,
                                self.target_layout,
                                inner,
                            )?;
                            Some(self.builder.declare_array_type(Type::I8, size))
                        })?;
                    Some(self.builder.objref_type(target_ty))
                }
                CapabilityKind::Mut => Some(self.pointer_like_sonatina_ty(inner, &[])),
                CapabilityKind::Ref if lowers_by_ref_layout(self.db, self.core, inner) => {
                    Some(self.pointer_like_sonatina_ty(inner, &[]))
                }
                CapabilityKind::Ref => Some(Type::I256),
            };
        }

        if let Some(target_ty) = memory_effect_pointer_target_ty(self.db, self.core, ty) {
            return Some(self.pointer_like_sonatina_ty(target_ty, &[]));
        }

        if let Some(inner) = mir::repr::transparent_newtype_field_ty(self.db, ty) {
            return self
                .fe_object_ty_to_sonatina_with_pointer_leaf_infos(inner, pointer_leaf_infos);
        }

        if matches!(
            mir::repr::repr_kind_for_ty(self.db, self.core, ty),
            mir::repr::ReprKind::Word
        ) {
            return Some(types::value_type(self.db, ty));
        }

        let base_ty = ty.base_ty(self.db);
        match base_ty.data(self.db) {
            TyData::TyBase(TyBase::Prim(prim)) => match prim {
                PrimTy::String => None,
                PrimTy::Tuple(_) => {
                    let field_tys = ty.field_types(self.db);
                    if field_tys.is_empty() {
                        return Some(Type::Unit);
                    }
                    let mut sonatina_fields = Vec::with_capacity(field_tys.len());
                    for (field_idx, field_ty) in field_tys.iter().copied().enumerate() {
                        let field_pointer_leaf_infos =
                            field_pointer_leaf_infos(pointer_leaf_infos, field_idx);
                        sonatina_fields.push(
                            self.fe_object_ty_to_sonatina_with_pointer_leaf_infos(
                                field_ty,
                                &field_pointer_leaf_infos,
                            )?,
                        );
                    }
                    let id = *self.name_counter;
                    *self.name_counter += 1;
                    Some(self.builder.declare_struct_type(
                        &format!("__fe_obj_tuple_{id}"),
                        &sonatina_fields,
                        false,
                    ))
                }
                PrimTy::Array => {
                    let elem_ty = layout::array_elem_ty(self.db, ty)?;
                    let len = layout::array_len(self.db, ty)?;
                    let elem_pointer_leaf_infos = array_elem_pointer_leaf_infos(pointer_leaf_infos);
                    let sonatina_elem = self.fe_object_ty_to_sonatina_with_pointer_leaf_infos(
                        elem_ty,
                        &elem_pointer_leaf_infos,
                    )?;
                    Some(self.builder.declare_array_type(sonatina_elem, len))
                }
                _ => Some(types::value_type(self.db, ty)),
            },
            TyData::TyBase(TyBase::Adt(adt_def)) => match adt_def.adt_ref(self.db) {
                AdtRef::Struct(_) => {
                    let field_tys = ty.field_types(self.db);
                    let mut sonatina_fields = Vec::with_capacity(field_tys.len());
                    for (field_idx, field_ty) in field_tys.iter().copied().enumerate() {
                        let field_pointer_leaf_infos =
                            field_pointer_leaf_infos(pointer_leaf_infos, field_idx);
                        sonatina_fields.push(
                            self.fe_object_ty_to_sonatina_with_pointer_leaf_infos(
                                field_ty,
                                &field_pointer_leaf_infos,
                            )?,
                        );
                    }
                    let name = adt_def
                        .adt_ref(self.db)
                        .name(self.db)
                        .map(|id| id.data(self.db).to_string())
                        .unwrap_or_else(|| "anon".to_string());
                    let id = *self.name_counter;
                    *self.name_counter += 1;
                    Some(self.builder.declare_struct_type(
                        &format!("__fe_obj_{name}_{id}"),
                        &sonatina_fields,
                        false,
                    ))
                }
                AdtRef::Enum(_) => self.declare_enum_type(ty, true, pointer_leaf_infos),
            },
            TyData::TyBase(TyBase::Contract(_)) | TyData::TyBase(TyBase::Func(_)) => {
                Some(Type::Unit)
            }
            _ => None,
        }
    }
}

/// Checks whether a projection chain is eligible for GEP-based addressing.
///
/// Returns true when all projections are Field or Index (no VariantField, Discriminant, or Deref).
fn projections_eligible_for_gep(projections: &[ResolvedPlaceProjection<'_>]) -> bool {
    projections
        .iter()
        .all(|step| matches!(step.projection, Projection::Field(_) | Projection::Index(_)))
}

fn place_supports_gep<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    mut current_sonatina_ty: Type,
    projections: &[ResolvedPlaceProjection<'db>],
) -> bool {
    for step in projections {
        match &step.projection {
            Projection::Field(field_idx) => {
                if mir::repr::transparent_field0_inner_ty(ctx.db, step.owner.ty, *field_idx)
                    == Some(step.result.ty)
                {
                    continue;
                }

                let Some(field_sonatina_ty) = ctx.fb.module_builder.ctx.with_ty_store(|s| {
                    s.struct_def(current_sonatina_ty)
                        .and_then(|sd| sd.fields.get(*field_idx).copied())
                }) else {
                    return false;
                };
                current_sonatina_ty = field_sonatina_ty;
            }
            Projection::Index(_) => {
                let Some(elem_sonatina_ty) = ctx
                    .fb
                    .module_builder
                    .ctx
                    .with_ty_store(|s| s.array_def(current_sonatina_ty).map(|(elem, _)| elem))
                else {
                    return false;
                };
                current_sonatina_ty = elem_sonatina_ty;
            }
            _ => return false,
        }
    }

    true
}

#[derive(Debug, Clone, Copy)]
enum LoweredPlaceAddr {
    Word(ValueId),
    MemoryPtr(ValueId),
    ObjectRef(ValueId),
}

#[derive(Debug, Clone, Copy)]
struct LoweredPlaceTerminal<'db> {
    state: PlaceState<'db>,
    addr: LoweredPlaceAddr,
}

impl<'db> LoweredPlaceTerminal<'db> {
    fn word_addr<C: sonatina_ir::func_cursor::FuncCursor>(
        self,
        ctx: &mut LowerCtx<'_, 'db, C>,
    ) -> ValueId {
        match self.addr {
            LoweredPlaceAddr::Word(addr) => addr,
            LoweredPlaceAddr::MemoryPtr(ptr) => coerce_value_to_word(ctx, ptr),
            LoweredPlaceAddr::ObjectRef(_) => unreachable!(
                "object-backed place must not be coerced to a raw word address without an explicit load"
            ),
        }
    }

    fn memory_ptr<C: sonatina_ir::func_cursor::FuncCursor>(
        self,
        ctx: &mut LowerCtx<'_, 'db, C>,
        expected_ty: Type,
    ) -> Option<ValueId> {
        match self.addr {
            LoweredPlaceAddr::MemoryPtr(ptr) => Some(coerce_value_to_type(ctx, ptr, expected_ty)),
            LoweredPlaceAddr::Word(_) | LoweredPlaceAddr::ObjectRef(_) => None,
        }
    }

    fn runtime_addr(self) -> ValueId {
        match self.addr {
            LoweredPlaceAddr::Word(addr)
            | LoweredPlaceAddr::MemoryPtr(addr)
            | LoweredPlaceAddr::ObjectRef(addr) => addr,
        }
    }

    fn native_memory_ptr(self) -> Option<ValueId> {
        match self.addr {
            LoweredPlaceAddr::MemoryPtr(ptr) => Some(ptr),
            LoweredPlaceAddr::Word(_) | LoweredPlaceAddr::ObjectRef(_) => None,
        }
    }

    fn object_ref(self) -> Option<ValueId> {
        match self.addr {
            LoweredPlaceAddr::ObjectRef(object_ref) => Some(object_ref),
            LoweredPlaceAddr::Word(_) | LoweredPlaceAddr::MemoryPtr(_) => None,
        }
    }
}

fn lower_place_state_terminal<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    debug_place: &Place<'db>,
    state: PlaceState<'db>,
    runtime: ValueId,
) -> Result<LoweredPlaceTerminal<'db>, LowerError> {
    let address_space = state.location_address_space().ok_or_else(|| {
        LowerError::Internal(format!("non-location segment base for {debug_place:?}"))
    })?;
    Ok(LoweredPlaceTerminal {
        state,
        addr: if matches!(address_space, AddressSpaceKind::Memory) {
            if ctx
                .fb
                .type_of(runtime)
                .is_obj_ref(&ctx.fb.module_builder.ctx)
            {
                LoweredPlaceAddr::ObjectRef(runtime)
            } else {
                LoweredPlaceAddr::MemoryPtr(
                    if ctx
                        .fb
                        .type_of(runtime)
                        .is_pointer(&ctx.fb.module_builder.ctx)
                    {
                        runtime
                    } else {
                        let opaque_ptr_ty = ctx.fb.ptr_type(Type::I8);
                        coerce_word_addr_to_ptr(ctx, runtime, opaque_ptr_ty)
                    },
                )
            }
        } else {
            LoweredPlaceAddr::Word(coerce_value_to_word(ctx, runtime))
        },
    })
}

fn resolve_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
) -> Result<ResolvedPlace<'db>, LowerError> {
    ctx.resolve_place(place).ok_or_else(|| {
        let base = ctx.body.value(place.base);
        LowerError::Internal(format!(
            "failed to resolve MIR place {place:?} (base ty={}, repr={:?}, origin={:?}, pointer_info={:?})",
            base.ty.pretty_print(ctx.db),
            base.repr,
            base.origin,
            base.pointer_info,
        ))
    })
}

fn place_yields_location_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    value_ty: TyId<'db>,
    pointer_info: Option<mir::ir::PointerInfo<'db>>,
) -> Result<bool, LowerError> {
    mir::repr::place_yields_location_value(
        ctx.db,
        ctx.core,
        &ctx.body.values,
        &ctx.body.locals,
        place,
        value_ty,
        pointer_info,
    )
    .ok_or_else(|| LowerError::Internal(format!("failed to resolve place for {place:?}")))
}

fn lower_place_runtime_location_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    expected_runtime_ty: Type,
) -> Result<ValueId, LowerError> {
    let terminal = lower_place_terminal(ctx, place)?;
    if let Some(value) = lower_object_ref_terminal_value(ctx, terminal, expected_runtime_ty)? {
        return Ok(value);
    }
    if expected_runtime_ty.is_pointer(&ctx.fb.module_builder.ctx)
        && let Some(memory_ptr) = terminal.memory_ptr(ctx, expected_runtime_ty)
    {
        return Ok(coerce_value_to_type(ctx, memory_ptr, expected_runtime_ty));
    }
    if terminal.object_ref().is_some() {
        return Err(LowerError::Internal(format!(
            "object-backed place location value requires object-ref runtime type for {place:?} (expected {expected_runtime_ty:?})"
        )));
    }
    let word_addr = terminal.word_addr(ctx);
    Ok(coerce_value_to_type(ctx, word_addr, expected_runtime_ty))
}

fn lower_object_ref_terminal_value<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    terminal: LoweredPlaceTerminal<'db>,
    expected_runtime_ty: Type,
) -> Result<Option<ValueId>, LowerError> {
    if !expected_runtime_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
        return Ok(None);
    }

    let Some(object_ref) = terminal.object_ref() else {
        return Ok(None);
    };
    let object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
    if object_elem_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
        let loaded = ctx
            .fb
            .insert_inst(ObjLoad::new(ctx.is, object_ref), object_elem_ty);
        return Ok(Some(coerce_value_to_type(ctx, loaded, expected_runtime_ty)));
    }
    Ok(Some(coerce_value_to_type(
        ctx,
        object_ref,
        expected_runtime_ty,
    )))
}

fn terminal_address_space<'db>(
    terminal: &LoweredPlaceTerminal<'db>,
    place: &Place<'db>,
) -> Result<AddressSpaceKind, LowerError> {
    terminal
        .state
        .location_address_space()
        .ok_or_else(|| LowerError::Internal(format!("store target is not a location: {place:?}")))
}

fn terminal_native_memory_ptr<'db>(
    terminal: &LoweredPlaceTerminal<'db>,
    place: &Place<'db>,
) -> Result<ValueId, LowerError> {
    terminal.native_memory_ptr().ok_or_else(|| {
        LowerError::Internal(format!(
            "memory place terminal missing pointer for {place:?}"
        ))
    })
}

fn store_word_to_terminal<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    terminal: LoweredPlaceTerminal<'db>,
    val: ValueId,
) -> Result<(), LowerError> {
    match terminal_address_space(&terminal, place)? {
        AddressSpaceKind::Memory => {
            if terminal.object_ref().is_some() {
                return Err(LowerError::Unsupported(
                    "word stores into object-backed memory places are not yet supported"
                        .to_string(),
                ));
            }
            ctx.fb.insert_inst_no_result(Mstore::new(
                ctx.is,
                terminal_native_memory_ptr(&terminal, place)?,
                val,
                Type::I256,
            ));
        }
        AddressSpaceKind::Storage => {
            let word_addr = terminal.word_addr(ctx);
            ctx.fb
                .insert_inst_no_result(EvmSstore::new(ctx.is, word_addr, val));
        }
        AddressSpaceKind::TransientStorage => {
            let word_addr = terminal.word_addr(ctx);
            ctx.fb
                .insert_inst_no_result(EvmTstore::new(ctx.is, word_addr, val));
        }
        AddressSpaceKind::Calldata => {
            return Err(LowerError::Unsupported("store to calldata".to_string()));
        }
        AddressSpaceKind::Code => {
            return Err(LowerError::Unsupported(
                "cannot store to code space".to_string(),
            ));
        }
    }
    Ok(())
}

fn load_from_terminal<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    terminal: LoweredPlaceTerminal<'db>,
    place: &Place<'db>,
    loaded_ty: TyId<'db>,
    expected_runtime_ty: Type,
    packed: bool,
) -> Result<ValueId, LowerError> {
    match terminal_address_space(&terminal, place)? {
        AddressSpaceKind::Memory => {
            if let Some(object_ref) = terminal.object_ref() {
                let object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
                if expected_runtime_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
                    if object_elem_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
                        let loaded = ctx
                            .fb
                            .insert_inst(ObjLoad::new(ctx.is, object_ref), object_elem_ty);
                        return Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty));
                    }
                    return Ok(coerce_value_to_type(ctx, object_ref, expected_runtime_ty));
                }
                let loaded = ctx
                    .fb
                    .insert_inst(ObjLoad::new(ctx.is, object_ref), object_elem_ty);
                return Ok(coerce_value_to_runtime_ty(
                    ctx,
                    loaded,
                    loaded_ty,
                    expected_runtime_ty,
                ));
            }
            let ptr_addr = terminal_native_memory_ptr(&terminal, place)?;
            if expected_runtime_ty.is_pointer(&ctx.fb.module_builder.ctx) && !packed {
                return Ok(ctx.fb.insert_inst(
                    Mload::new(ctx.is, ptr_addr, expected_runtime_ty),
                    expected_runtime_ty,
                ));
            }
            let word = ctx
                .fb
                .insert_inst(Mload::new(ctx.is, ptr_addr, Type::I256), Type::I256);
            let raw = if packed {
                extract_evm_byte(ctx.fb, ctx.is, 0, word)
            } else {
                word
            };
            Ok(apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is))
        }
        AddressSpaceKind::Storage => {
            let word_addr = terminal.word_addr(ctx);
            let raw = ctx
                .fb
                .insert_inst(EvmSload::new(ctx.is, word_addr), Type::I256);
            let loaded = apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is);
            Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty))
        }
        AddressSpaceKind::TransientStorage => {
            let word_addr = terminal.word_addr(ctx);
            let raw = ctx
                .fb
                .insert_inst(EvmTload::new(ctx.is, word_addr), Type::I256);
            let loaded = apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is);
            Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty))
        }
        AddressSpaceKind::Calldata => {
            let word_addr = terminal.word_addr(ctx);
            let raw = ctx
                .fb
                .insert_inst(EvmCalldataLoad::new(ctx.is, word_addr), Type::I256);
            let loaded = apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is);
            Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty))
        }
        AddressSpaceKind::Code => {
            let word_addr = terminal.word_addr(ctx);
            let copy_size = if packed { 1 } else { 32 };
            let size_val = ctx.fb.make_imm_value(I256::from(copy_size));
            let scratch = emit_alloca_word_addr(ctx.fb, Type::I256, ctx.is);
            ctx.fb
                .insert_inst_no_result(EvmCodeCopy::new(ctx.is, scratch, word_addr, size_val));
            let word = ctx
                .fb
                .insert_inst(Mload::new(ctx.is, scratch, Type::I256), Type::I256);
            let raw = if packed {
                extract_evm_byte(ctx.fb, ctx.is, 0, word)
            } else {
                word
            };
            let loaded = apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is);
            Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty))
        }
    }
}

fn split_place_discriminant_tail<'db>(place: &Place<'db>) -> Option<Place<'db>> {
    let tail = place.projection.iter().last()?.clone();
    if !matches!(tail, Projection::Discriminant) {
        return None;
    }
    let mut owner_projection = mir::MirProjectionPath::new();
    for projection in place
        .projection
        .iter()
        .take(place.projection.len().saturating_sub(1))
    {
        owner_projection.push(projection.clone());
    }
    Some(Place::new(place.base, owner_projection))
}

fn sonatina_enum_variant_ref<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    sonatina_enum_ty: Type,
    variant_idx: usize,
) -> Result<EnumVariantRef, LowerError> {
    let Type::Compound(cmpd_ref) = sonatina_enum_ty else {
        return Err(LowerError::Internal(format!(
            "expected Sonatina enum compound type, found {sonatina_enum_ty:?}"
        )));
    };
    let variant_ref = EnumVariantRef::new(cmpd_ref, variant_idx as u32);
    if ctx
        .fb
        .module_builder
        .ctx
        .with_ty_store(|s| s.enum_variant_data(variant_ref).is_some())
    {
        Ok(variant_ref)
    } else {
        Err(LowerError::Internal(format!(
            "enum variant index {variant_idx} is out of bounds for {sonatina_enum_ty:?}"
        )))
    }
}

fn enum_variant_field_ty<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    sonatina_enum_ty: Type,
    variant_ref: EnumVariantRef,
    field_idx: usize,
) -> Result<Type, LowerError> {
    ctx.fb
        .module_builder
        .ctx
        .with_ty_store(|s| {
            s.enum_variant_data(variant_ref)
                .and_then(|variant| variant.fields.get(field_idx).copied())
        })
        .ok_or_else(|| {
            LowerError::Internal(format!(
                "enum field {field_idx} is out of bounds for variant {:?} of {sonatina_enum_ty:?}",
                variant_ref.index()
            ))
        })
}

fn lower_enum_owner_object_ref<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    owner_place: &Place<'db>,
) -> Result<Option<ValueId>, LowerError> {
    if mir::repr::place_object_ref_target_ty(
        ctx.db,
        ctx.core,
        &ctx.body.values,
        &ctx.body.locals,
        owner_place,
    )
    .filter(|enum_ty| enum_ty.as_enum(ctx.db).is_some())
    .is_none()
    {
        return Ok(None);
    }
    let terminal = lower_place_terminal(ctx, owner_place)?;
    Ok(terminal.object_ref())
}

fn lower_enum_discriminant_load<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    expected_runtime_ty: Type,
) -> Result<Option<ValueId>, LowerError> {
    let Some(owner_place) = split_place_discriminant_tail(place) else {
        return Ok(None);
    };
    let Some(object_ref) = lower_enum_owner_object_ref(ctx, &owner_place)? else {
        return Ok(None);
    };
    if !expected_runtime_ty.is_enum_tag() {
        return Err(LowerError::Unsupported(format!(
            "object-backed enum discriminant load requires enum-tag runtime type for {place:?}"
        )));
    }
    Ok(Some(ctx.fb.insert_inst(
        EnumGetTag::new(ctx.is, object_ref),
        expected_runtime_ty,
    )))
}

fn lower_enum_set_tag_for_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    variant: hir::hir_def::EnumVariant<'db>,
) -> Result<bool, LowerError> {
    let Some(object_ref) = lower_enum_owner_object_ref(ctx, place)? else {
        return Ok(false);
    };
    let sonatina_enum_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
    let variant_ref = sonatina_enum_variant_ref(ctx, sonatina_enum_ty, variant.idx.into())?;
    ctx.fb
        .insert_inst_no_result(EnumSetTag::new(ctx.is, object_ref, variant_ref));
    Ok(true)
}

fn lower_enum_discriminant_store<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    variant_idx: usize,
) -> Result<bool, LowerError> {
    let Some(owner_place) = split_place_discriminant_tail(place) else {
        return Ok(false);
    };
    let Some(object_ref) = lower_enum_owner_object_ref(ctx, &owner_place)? else {
        return Ok(false);
    };
    let sonatina_enum_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
    let variant_ref = sonatina_enum_variant_ref(ctx, sonatina_enum_ty, variant_idx)?;
    ctx.fb
        .insert_inst_no_result(EnumSetTag::new(ctx.is, object_ref, variant_ref));
    Ok(true)
}

fn lower_object_place_segment<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    segment_base: ValueId,
    segment: &ResolvedPlaceSegment<'db>,
) -> Result<LoweredPlaceTerminal<'db>, LowerError> {
    let mut object_ref = segment_base;
    let mut object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;

    for step in &segment.projections {
        match &step.projection {
            Projection::Field(field_idx) => {
                if mir::repr::transparent_field0_inner_ty(ctx.db, step.owner.ty, *field_idx)
                    == Some(step.result.ty)
                {
                    continue;
                }

                let idx = ctx.fb.make_imm_value(I256::from(*field_idx as u64));
                object_elem_ty = sonatina_struct_field_ty(
                    ctx,
                    object_elem_ty,
                    *field_idx,
                    step.owner.ty,
                    step.result.ty,
                )?;
                let result_ty = ctx.fb.module_builder.objref_type(object_elem_ty);
                object_ref = ctx.fb.insert_inst(
                    ObjProj::new(ctx.is, smallvec1::smallvec![object_ref, idx]),
                    result_ty,
                );
            }
            Projection::Index(idx_source) => {
                let idx = lower_array_index_with_bounds_check(ctx, step.owner.ty, idx_source)?;
                object_elem_ty = sonatina_array_elem_ty(ctx, object_elem_ty)?;
                let result_ty = ctx.fb.module_builder.objref_type(object_elem_ty);
                object_ref = ctx
                    .fb
                    .insert_inst(ObjIndex::new(ctx.is, object_ref, idx), result_ty);
            }
            Projection::VariantField {
                variant,
                enum_ty: _,
                field_idx,
            } => {
                let field_idx_val = ctx.fb.make_imm_value(I256::from(*field_idx as u64));
                let variant_ref =
                    sonatina_enum_variant_ref(ctx, object_elem_ty, variant.idx.into())?;
                object_elem_ty =
                    enum_variant_field_ty(ctx, object_elem_ty, variant_ref, *field_idx)?;
                let result_ty = ctx.fb.module_builder.objref_type(object_elem_ty);
                object_ref = ctx.fb.insert_inst(
                    EnumAssertVariantRef::new(ctx.is, object_ref, variant_ref),
                    ctx.fb.func.dfg.value_ty(object_ref),
                );
                object_ref = ctx.fb.insert_inst(
                    EnumProj::new(ctx.is, object_ref, variant_ref, field_idx_val),
                    result_ty,
                );
            }
            Projection::Discriminant => {
                return Err(LowerError::Unsupported(format!(
                    "object-backed enum discriminant projections are handled directly for {segment:?}"
                )));
            }
            Projection::Deref => {
                return Err(LowerError::Unsupported(
                    "object-backed dereference projection is not implemented".to_string(),
                ));
            }
        }
    }

    Ok(LoweredPlaceTerminal {
        state: segment.terminal_state(),
        addr: LoweredPlaceAddr::ObjectRef(object_ref),
    })
}

fn lower_place_segment_terminal<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    debug_place: &Place<'db>,
    segment_base: ValueId,
    segment: &ResolvedPlaceSegment<'db>,
) -> Result<LoweredPlaceTerminal<'db>, LowerError> {
    let address_space = segment.base.location_address_space().ok_or_else(|| {
        LowerError::Internal(format!("non-location segment base for {debug_place:?}"))
    })?;
    if segment.projections.is_empty() {
        return lower_place_state_terminal(
            ctx,
            debug_place,
            segment.terminal_state(),
            segment_base,
        );
    }
    if matches!(address_space, AddressSpaceKind::Memory)
        && ctx
            .fb
            .type_of(segment_base)
            .is_obj_ref(&ctx.fb.module_builder.ctx)
    {
        return lower_object_place_segment(ctx, segment_base, segment);
    }

    let is_slot_addressed = matches!(
        address_space,
        AddressSpaceKind::Storage | AddressSpaceKind::TransientStorage
    );
    if !is_slot_addressed
        && projections_eligible_for_gep(&segment.projections)
        && !layout::resolved_place_requires_packed_layout_arithmetic(
            ctx.db,
            segment.base.ty,
            &segment.projections,
        )
        .map_err(LowerError::Unsupported)?
        && let Some(sonatina_ty) = ctx.type_lowerer().fe_ty_to_sonatina(segment.base.ty)
        && place_supports_gep(ctx, sonatina_ty, &segment.projections)
    {
        let gep_ptr =
            lower_place_address_gep(ctx, &segment.projections, segment_base, sonatina_ty)?;
        return Ok(LoweredPlaceTerminal {
            state: segment.terminal_state(),
            addr: LoweredPlaceAddr::MemoryPtr(gep_ptr),
        });
    }

    if ctx
        .fb
        .type_of(segment_base)
        .is_obj_ref(&ctx.fb.module_builder.ctx)
    {
        return Err(LowerError::Internal(format!(
            "object-backed place segment did not lower through the object path for {debug_place:?}",
        )));
    }
    let base_word = coerce_value_to_word(ctx, segment_base);
    let word_addr =
        lower_place_address_arithmetic(ctx, &segment.projections, base_word, is_slot_addressed)?;
    Ok(LoweredPlaceTerminal {
        state: segment.terminal_state(),
        addr: if matches!(address_space, AddressSpaceKind::Memory) {
            {
                let opaque_ptr_ty = ctx.fb.ptr_type(Type::I8);
                LoweredPlaceAddr::MemoryPtr(coerce_word_addr_to_ptr(ctx, word_addr, opaque_ptr_ty))
            }
        } else {
            LoweredPlaceAddr::Word(word_addr)
        },
    })
}

fn terminal_runtime_value<'db>(terminal: LoweredPlaceTerminal<'db>) -> ValueId {
    terminal.runtime_addr()
}

fn place_before_deref_segment<'db>(
    place: &Place<'db>,
    segments: &[ResolvedPlaceSegment<'db>],
    segment_idx: usize,
) -> Place<'db> {
    let mut projection = mir::MirProjectionPath::new();
    for segment in segments.iter().take(segment_idx) {
        if segment.start_kind.is_some() {
            projection.push(Projection::Deref);
        }
        for step in &segment.projections {
            projection.push(step.projection.clone());
        }
    }
    Place::new(place.base, projection)
}

fn lower_place_terminal<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
) -> Result<LoweredPlaceTerminal<'db>, LowerError> {
    let resolved = resolve_place(ctx, place)?;
    let root_runtime = match ctx.body.value(place.base).origin {
        mir::ValueOrigin::Local(local) => {
            if let Some(place_root) = materialized_local_place_root(ctx, local) {
                match place_root {
                    MaterializedLocalPlaceRoot::MemorySlot(slot_ptr) => slot_ptr,
                    MaterializedLocalPlaceRoot::ObjectRoot(object_ref) => object_ref,
                }
            } else {
                let root_local = ctx.body.spill_slots.get(&local).copied().unwrap_or(local);
                let var = ctx.local_vars.get(&root_local).copied().ok_or_else(|| {
                    LowerError::Internal(format!(
                        "SSA variable not found for place root {root_local:?}"
                    ))
                })?;
                ctx.fb.use_var(var)
            }
        }
        _ => lower_value(ctx, place.base)?,
    };
    let mut current_terminal: Option<LoweredPlaceTerminal<'db>> = None;

    for (idx, segment) in resolved.segments.iter().enumerate() {
        let segment_base_runtime = match (idx == 0, segment.start_kind, current_terminal.take()) {
            (true, None, None)
            | (true, Some(mir::repr::DerefStepKind::ReuseLocation), None)
            | (true, Some(mir::repr::DerefStepKind::UseBaseValue), None) => root_runtime,
            (true, Some(mir::repr::DerefStepKind::LoadLocationValue), None) => {
                let base_terminal =
                    lower_place_state_terminal(ctx, place, segment.before, root_runtime)?;
                let boundary_place = place_before_deref_segment(place, &resolved.segments, idx);
                let runtime_ty =
                    deref_boundary_runtime_ty(ctx, &boundary_place, segment.before.ty)?;
                load_from_terminal(
                    ctx,
                    base_terminal,
                    place,
                    segment.before.ty,
                    runtime_ty,
                    false,
                )?
            }
            (false, Some(mir::repr::DerefStepKind::ReuseLocation), Some(terminal)) => {
                terminal_runtime_value(terminal)
            }
            (false, Some(mir::repr::DerefStepKind::LoadLocationValue), Some(terminal)) => {
                let boundary_place = place_before_deref_segment(place, &resolved.segments, idx);
                let runtime_ty =
                    deref_boundary_runtime_ty(ctx, &boundary_place, segment.before.ty)?;
                load_from_terminal(ctx, terminal, place, segment.before.ty, runtime_ty, false)?
            }
            (false, None, Some(_))
            | (false, Some(mir::repr::DerefStepKind::UseBaseValue), Some(_))
            | (true, None, Some(_))
            | (true, Some(_), Some(_))
            | (false, _, None) => {
                return Err(LowerError::Internal(format!(
                    "invalid resolved place segment sequence for {place:?}"
                )));
            }
        };
        current_terminal = Some(lower_place_segment_terminal(
            ctx,
            place,
            segment_base_runtime,
            segment,
        )?);
    }

    current_terminal.ok_or_else(|| {
        LowerError::Internal(format!("resolved place produced no segments for {place:?}"))
    })
}

fn deref_boundary_runtime_ty<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    loaded_ty: TyId<'db>,
) -> Result<Type, LowerError> {
    ctx.runtime_type_for_loaded_place(place, loaded_ty)
}

/// Computes the address for a place by walking the projection path.
///
/// For memory, computes byte offsets. For storage, computes slot offsets.
/// Returns a Sonatina ValueId representing the final address.
fn lower_place_address<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
) -> Result<ValueId, LowerError> {
    let lowered = lower_place_terminal(ctx, place)?;
    if lowered.object_ref().is_some() {
        return Err(LowerError::Unsupported(format!(
            "raw address materialization is not supported for object-backed place {place:?}"
        )));
    }
    Ok(lowered.word_addr(ctx))
}

/// GEP-based place address computation for memory-addressed struct/array paths.
fn lower_place_address_gep<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    projections: &[ResolvedPlaceProjection<'db>],
    base_val: ValueId,
    base_sonatina_ty: Type,
) -> Result<ValueId, LowerError> {
    let ptr_ty = ctx.fb.ptr_type(base_sonatina_ty);

    // Reuse pointer sources from `ptr_to_int` when possible to avoid pointless
    // `ptr_to_int -> int_to_ptr` round-trips before GEP.
    let typed_ptr = coerce_word_addr_to_ptr(ctx, base_val, ptr_ty);

    // Build GEP index list, tracking types through the chain
    let mut gep_values: SmallVec<[ValueId; 8]> = SmallVec::new();
    gep_values.push(typed_ptr);

    // Initial dereference index (standard GEP convention: index 0 dereferences the pointer)
    let zero = ctx.fb.make_imm_value(I256::zero());
    gep_values.push(zero);

    let mut current_sonatina_ty = base_sonatina_ty;

    for step in projections {
        match &step.projection {
            Projection::Field(field_idx) => {
                let owner_fe_ty = step.owner.ty;
                if let Some(inner_ty) =
                    mir::repr::transparent_field0_inner_ty(ctx.db, owner_fe_ty, *field_idx)
                    && inner_ty == step.result.ty
                {
                    continue;
                }

                let idx_val = ctx.fb.make_imm_value(I256::from(*field_idx as u64));
                gep_values.push(idx_val);

                // Navigate Fe type
                // Navigate sonatina type to the field's type
                current_sonatina_ty = sonatina_struct_field_ty(
                    ctx,
                    current_sonatina_ty,
                    *field_idx,
                    owner_fe_ty,
                    step.result.ty,
                )?;
            }
            Projection::Index(idx_source) => {
                // Bounds check: revert if index >= array length
                let arr_len = layout::array_len(ctx.db, step.owner.ty);
                let idx_val = match idx_source {
                    IndexSource::Constant(idx) => {
                        if let Some(len) = arr_len
                            && *idx >= len
                        {
                            let revert_block =
                                ensure_panic_revert_block(ctx, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
                            ctx.fb
                                .insert_inst_no_result(Jump::new(ctx.is, revert_block));
                            let unreachable_block = ctx.fb.append_block();
                            ctx.fb.switch_to_block(unreachable_block);
                        }
                        ctx.fb.make_imm_value(I256::from(*idx as u64))
                    }
                    IndexSource::Dynamic(value_id) => {
                        let val = lower_value(ctx, *value_id)?;
                        if let Some(len) = arr_len {
                            let len_val = ctx.fb.make_imm_value(I256::from(len as u64));
                            let in_bounds =
                                ctx.fb.insert_inst(Lt::new(ctx.is, val, len_val), Type::I1);
                            let oob = ctx.fb.insert_inst(IsZero::new(ctx.is, in_bounds), Type::I1);
                            emit_panic_revert(ctx, oob, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
                        }
                        val
                    }
                };
                gep_values.push(idx_val);

                // Navigate sonatina type to array element
                current_sonatina_ty = sonatina_array_elem_ty(ctx, current_sonatina_ty)?;
            }
            _ => unreachable!("projections_eligible_for_gep ensures only Field/Index"),
        }
    }

    // The GEP result is a pointer to the final element type
    let result_ptr_ty = ctx.fb.ptr_type(current_sonatina_ty);
    let gep_result = ctx
        .fb
        .insert_inst(Gep::new(ctx.is, gep_values), result_ptr_ty);

    Ok(gep_result)
}

/// Resolves the sonatina type of a struct field by index.
fn sonatina_struct_field_ty<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    struct_ty: Type,
    field_idx: usize,
    owner_fe_ty: hir::analysis::ty::ty_def::TyId<'_>,
    field_fe_ty: hir::analysis::ty::ty_def::TyId<'_>,
) -> Result<Type, LowerError> {
    let fields = ctx
        .fb
        .module_builder
        .ctx
        .with_ty_store(|s| s.struct_def(struct_ty).map(|sd| sd.fields.clone()));
    match fields {
        Some(f) => f.get(field_idx).copied().ok_or_else(|| {
            LowerError::Internal(format!(
                "gep: sonatina struct field {field_idx} out of bounds"
            ))
        }),
        None => {
            let compound = struct_ty.resolve_compound(&ctx.fb.module_builder.ctx);
            Err(LowerError::Internal(format!(
                "gep: expected sonatina struct type for Field projection, got {struct_ty:?} / {compound:?} while projecting field {field_idx} of {} (field type {})",
                owner_fe_ty.pretty_print(ctx.db),
                field_fe_ty.pretty_print(ctx.db)
            )))
        }
    }
}

/// Resolves the sonatina element type of an array type.
fn sonatina_array_elem_ty<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    array_ty: Type,
) -> Result<Type, LowerError> {
    let elem = ctx
        .fb
        .module_builder
        .ctx
        .with_ty_store(|s| s.array_def(array_ty).map(|(elem, _len)| elem));
    match elem {
        Some(e) => Ok(e),
        None => Err(LowerError::Internal(
            "gep: expected sonatina array type for Index projection".to_string(),
        )),
    }
}

fn object_ref_elem_ty<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    object_ref_ty: Type,
) -> Result<Type, LowerError> {
    let Some(cmpd) = object_ref_ty.resolve_compound(&ctx.fb.module_builder.ctx) else {
        return Err(LowerError::Internal(format!(
            "expected object reference type, found {object_ref_ty:?}"
        )));
    };
    let sonatina_ir::types::CompoundType::ObjRef(elem_ty) = cmpd else {
        return Err(LowerError::Internal(format!(
            "expected object reference type, found {object_ref_ty:?}"
        )));
    };
    Ok(elem_ty)
}

fn lower_array_index_with_bounds_check<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    array_ty: TyId<'db>,
    idx_source: &IndexSource<mir::ValueId>,
) -> Result<ValueId, LowerError> {
    let arr_len = layout::array_len(ctx.db, array_ty).ok_or_else(|| {
        LowerError::Unsupported(format!(
            "projection: array index on non-array type `{}`",
            array_ty.pretty_print(ctx.db),
        ))
    })?;

    match idx_source {
        IndexSource::Constant(idx) => {
            if *idx >= arr_len {
                let revert_block = ensure_panic_revert_block(ctx, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
                ctx.fb
                    .insert_inst_no_result(Jump::new(ctx.is, revert_block));
                let unreachable_block = ctx.fb.append_block();
                ctx.fb.switch_to_block(unreachable_block);
            }
            Ok(ctx.fb.make_imm_value(I256::from(*idx as u64)))
        }
        IndexSource::Dynamic(value_id) => {
            let idx = lower_value(ctx, *value_id)?;
            let len_val = ctx.fb.make_imm_value(I256::from(arr_len as u64));
            let in_bounds = ctx.fb.insert_inst(Lt::new(ctx.is, idx, len_val), Type::I1);
            let oob = ctx.fb.insert_inst(IsZero::new(ctx.is, in_bounds), Type::I1);
            emit_panic_revert(ctx, oob, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
            Ok(idx)
        }
    }
}

/// Manual offset arithmetic path for place address computation.
/// Used for storage-addressed places and any memory path with enum projections.
fn lower_place_address_arithmetic<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    projections: &[ResolvedPlaceProjection<'db>],
    mut base_val: ValueId,
    is_slot_addressed: bool,
) -> Result<ValueId, LowerError> {
    let mut total_offset: usize = 0;

    for step in projections {
        match &step.projection {
            Projection::Field(field_idx) => {
                if mir::repr::transparent_field0_inner_ty(ctx.db, step.owner.ty, *field_idx)
                    == Some(step.result.ty)
                {
                    continue;
                }
                // Use slot-based offsets for storage, byte-based for memory
                total_offset += if is_slot_addressed {
                    layout::field_offset_slots(ctx.db, step.owner.ty, *field_idx)
                } else {
                    layout::field_offset_memory_in(
                        ctx.db,
                        ctx.target_layout,
                        step.owner.ty,
                        *field_idx,
                    )
                };
            }
            Projection::VariantField {
                variant,
                enum_ty,
                field_idx,
            } => {
                // Skip discriminant then compute field offset
                if is_slot_addressed {
                    total_offset += 1; // discriminant takes one slot
                    total_offset +=
                        layout::variant_field_offset_slots(ctx.db, *enum_ty, *variant, *field_idx);
                } else {
                    total_offset += ctx.target_layout.discriminant_size_bytes;
                    total_offset += layout::variant_field_offset_memory_in(
                        ctx.db,
                        ctx.target_layout,
                        *enum_ty,
                        *variant,
                        *field_idx,
                    );
                }
            }
            Projection::Discriminant => {
                // Discriminant is always at offset 0.
            }
            Projection::Index(idx_source) => {
                let stride = if is_slot_addressed {
                    layout::array_elem_stride_slots(ctx.db, step.owner.ty)
                } else {
                    layout::array_elem_stride_memory_in(ctx.db, ctx.target_layout, step.owner.ty)
                }
                .ok_or_else(|| {
                    LowerError::Unsupported(format!(
                        "projection: array index on non-array type `{}`",
                        step.owner.ty.pretty_print(ctx.db),
                    ))
                })?;

                // Get the array length for bounds checking
                let arr_len = layout::array_len(ctx.db, step.owner.ty);

                match idx_source {
                    IndexSource::Constant(idx) => {
                        // Compile-time bounds check for constant indices
                        if let Some(len) = arr_len
                            && *idx >= len
                        {
                            let revert_block =
                                ensure_panic_revert_block(ctx, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
                            ctx.fb
                                .insert_inst_no_result(Jump::new(ctx.is, revert_block));
                            let unreachable_block = ctx.fb.append_block();
                            ctx.fb.switch_to_block(unreachable_block);
                        }
                        total_offset += idx * stride;
                    }
                    IndexSource::Dynamic(value_id) => {
                        // Flush accumulated offset first
                        if total_offset != 0 {
                            let offset_val = ctx.fb.make_imm_value(I256::from(total_offset as u64));
                            base_val = ctx
                                .fb
                                .insert_inst(Add::new(ctx.is, base_val, offset_val), Type::I256);
                            total_offset = 0;
                        }

                        // Bounds check: revert if index >= array length
                        let idx_val = lower_value(ctx, *value_id)?;
                        if let Some(len) = arr_len {
                            let len_val = ctx.fb.make_imm_value(I256::from(len as u64));
                            // idx < len → 1 (in bounds) → IsZero → 0 (don't revert)
                            // idx >= len → 0 (OOB) → IsZero → 1 (revert)
                            let in_bounds = ctx
                                .fb
                                .insert_inst(Lt::new(ctx.is, idx_val, len_val), Type::I1);
                            let oob = ctx.fb.insert_inst(IsZero::new(ctx.is, in_bounds), Type::I1);
                            emit_panic_revert(ctx, oob, PANIC_CODE_INDEX_OUT_OF_BOUNDS)?;
                        }

                        // Compute dynamic index offset: idx * stride
                        let offset_val = if stride == 1 {
                            idx_val
                        } else {
                            let stride_val = ctx.fb.make_imm_value(I256::from(stride as u64));
                            ctx.fb
                                .insert_inst(Mul::new(ctx.is, idx_val, stride_val), Type::I256)
                        };
                        base_val = ctx
                            .fb
                            .insert_inst(Add::new(ctx.is, base_val, offset_val), Type::I256);
                    }
                }
            }
            Projection::Deref => {
                return Err(LowerError::Unsupported(
                    "projection: pointer dereference not implemented".to_string(),
                ));
            }
        }
    }

    // Add any remaining accumulated offset
    if total_offset != 0 {
        let offset_val = ctx.fb.make_imm_value(I256::from(total_offset as u64));
        base_val = ctx
            .fb
            .insert_inst(Add::new(ctx.is, base_val, offset_val), Type::I256);
    }

    Ok(base_val)
}

/// Lower a block terminator.
///
/// If `is_entry` is true, `Return` terminators emit `evm_stop` instead of internal `Return`,
/// since the entry function is executed directly by the EVM and must halt with an EVM opcode.
pub(super) fn lower_terminator<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    term: &mir::Terminator<'db>,
) -> Result<(), LowerError> {
    use mir::Terminator;

    match term {
        Terminator::Return { value: ret_val, .. } => {
            if ctx.is_entry {
                // Entry function: emit evm_stop to halt EVM execution.
                // Any return value is ignored since the entry function should have
                // already written return data via evm_return if needed.
                ctx.fb.insert_inst_no_result(EvmStop::new(ctx.is));
            } else {
                // Non-entry function: emit internal Return for function call semantics.
                let ret_sonatina = if let Some(v) = ret_val {
                    let ret_ty = ctx.current_function_metadata.ret.ok_or_else(|| {
                        LowerError::Internal(
                            "return value present but current function has no runtime return type"
                                .to_string(),
                        )
                    })?;
                    let value_ty = ctx
                        .body
                        .values
                        .get(v.index())
                        .ok_or_else(|| LowerError::Internal("unknown return value".to_string()))?
                        .ty;
                    let value = lower_value(ctx, *v)?;
                    Some(coerce_value_to_runtime_ty(ctx, value, value_ty, ret_ty))
                } else {
                    None
                };
                let ret_args = ret_sonatina
                    .map(|value| smallvec1::smallvec![value].into())
                    .unwrap_or_default();
                ctx.fb.insert_inst_no_result(Return::new(ctx.is, ret_args));
            }
        }
        Terminator::Goto { target, .. } => {
            let target_block = ctx.block_map[target];
            ctx.fb
                .insert_inst_no_result(Jump::new(ctx.is, target_block));
        }
        Terminator::Branch {
            cond,
            then_bb,
            else_bb,
            ..
        } => {
            let cond_val = lower_value(ctx, *cond)?;
            let cond_i1 = condition_to_i1(ctx.fb, cond_val, ctx.is);
            let then_block = ctx.block_map[then_bb];
            let else_block = ctx.block_map[else_bb];
            // Br: cond, nz_dest (then), z_dest (else)
            ctx.fb
                .insert_inst_no_result(Br::new(ctx.is, cond_i1, then_block, else_block));
        }
        Terminator::Switch {
            discr,
            targets,
            default,
            ..
        } => {
            let discr_val = lower_value(ctx, *discr)?;
            let default_block = ctx.block_map[default];

            if targets.is_empty() {
                ctx.fb
                    .insert_inst_no_result(Jump::new(ctx.is, default_block));
                return Ok(());
            }

            let discr_ty = ctx.fb.type_of(discr_val);
            let mut cases = Vec::with_capacity(targets.len());
            for target in targets {
                let value = make_int_immediate(
                    ctx.fb,
                    biguint_to_i256(&target.value.as_biguint()),
                    discr_ty,
                );
                let dest = ctx.block_map[&target.block];
                cases.push((value, dest));
            }

            ctx.fb.insert_inst_no_result(BrTable::new(
                ctx.is,
                discr_val,
                Some(default_block),
                cases,
            ));
        }
        Terminator::TerminatingCall { call, .. } => match call {
            mir::TerminatingCall::Call(call) => {
                let callee_name = call.resolved_name.as_ref().ok_or_else(|| {
                    LowerError::Unsupported("terminating call without resolved name".to_string())
                })?;

                if call.effect_args.is_empty() {
                    match callee_name.as_str() {
                        "stop" => {
                            if !call.args.is_empty() {
                                return Err(LowerError::Internal(
                                    "stop takes no arguments".to_string(),
                                ));
                            }
                            ctx.fb.insert_inst_no_result(EvmStop::new(ctx.is));
                            return Ok(());
                        }
                        "selfdestruct" => {
                            let [addr] = call.args.as_slice() else {
                                return Err(LowerError::Internal(
                                    "selfdestruct requires 1 argument".to_string(),
                                ));
                            };
                            let addr = lower_value(ctx, *addr)?;
                            let addr = coerce_value_to_word(ctx, addr);
                            ctx.fb
                                .insert_inst_no_result(EvmSelfDestruct::new(ctx.is, addr));
                            return Ok(());
                        }
                        _ => {}
                    }
                }

                if let Some(builtin) = call.builtin_terminator {
                    match builtin {
                        BuiltinTerminatorKind::Abort | BuiltinTerminatorKind::AbortWithValue => {
                            let zero = ctx.fb.make_imm_value(I256::zero());
                            ctx.fb
                                .insert_inst_no_result(EvmRevert::new(ctx.is, zero, zero));
                            return Ok(());
                        }
                    }
                }

                let Some(func_ref) = ctx.name_map.get(callee_name) else {
                    return Err(LowerError::Internal(format!(
                        "missing sonatina callee for terminating call: {callee_name}"
                    )));
                };

                let args = lower_call_args(
                    ctx,
                    callee_name,
                    &call.args,
                    &call.effect_args,
                    *func_ref,
                    "terminating call",
                )?;

                ctx.fb
                    .insert_inst_no_result(Call::new(ctx.is, *func_ref, args.into()));
                ctx.fb.insert_inst_no_result(EvmInvalid::new(ctx.is));
            }
            mir::TerminatingCall::Intrinsic { op, args } => {
                let mut lowered_args = Vec::with_capacity(args.len());
                for &arg in args {
                    lowered_args.push(lower_value(ctx, arg)?);
                }
                match op {
                    IntrinsicOp::ReturnData => {
                        let [addr, len] = lowered_args.as_slice() else {
                            return Err(LowerError::Internal(
                                "return_data requires 2 arguments".to_string(),
                            ));
                        };
                        let addr = coerce_value_to_word(ctx, *addr);
                        ctx.fb
                            .insert_inst_no_result(EvmReturn::new(ctx.is, addr, *len));
                    }
                    IntrinsicOp::Revert => {
                        let [addr, len] = lowered_args.as_slice() else {
                            return Err(LowerError::Internal(
                                "revert requires 2 arguments".to_string(),
                            ));
                        };
                        let addr = coerce_value_to_word(ctx, *addr);
                        ctx.fb
                            .insert_inst_no_result(EvmRevert::new(ctx.is, addr, *len));
                    }
                    _ => {
                        return Err(LowerError::Unsupported(format!(
                            "terminating intrinsic: {:?}",
                            op
                        )));
                    }
                }
            }
        },
        Terminator::Unreachable { .. } => {
            // Emit INVALID opcode (0xFE) - this consumes all gas and reverts
            ctx.fb.insert_inst_no_result(EvmInvalid::new(ctx.is));
        }
    }

    Ok(())
}

fn lower_alloc<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    dest: mir::LocalId,
    address_space: AddressSpaceKind,
) -> Result<ValueId, LowerError> {
    if !matches!(address_space, AddressSpaceKind::Memory) {
        return Err(LowerError::Unsupported(
            "typed alloc is only supported for memory".to_string(),
        ));
    }

    let alloc_ty = ctx
        .body
        .locals
        .get(dest.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown local: {dest:?}")))?
        .ty;

    let Some(size_bytes) = layout::ty_memory_size_or_word_in(ctx.db, ctx.target_layout, alloc_ty)
    else {
        return Err(LowerError::Unsupported(format!(
            "cannot determine allocation size for `{}`",
            alloc_ty.pretty_print(ctx.db)
        )));
    };

    if size_bytes == 0 {
        return Ok(zero_value_for_type(
            ctx.fb,
            ctx.local_runtime_types[dest.index()],
            ctx.is,
        ));
    }
    if !ctx.local_runtime_types[dest.index()].is_obj_ref(&ctx.fb.module_builder.ctx) {
        if !mir::repr::supports_object_ref_runtime_ty(ctx.db, ctx.core, alloc_ty) {
            let size = ctx.fb.make_imm_value(I256::from(size_bytes as u64));
            let ptr = emit_evm_malloc_ptr(ctx.fb, size, ctx.is);
            return Ok(coerce_value_to_type(
                ctx,
                ptr,
                ctx.local_runtime_types[dest.index()],
            ));
        }
        let slot_ty = ctx.fb.declare_array_type(Type::I8, size_bytes);
        let ptr = emit_alloca_ptr(ctx.fb, slot_ty, ctx.is);
        return Ok(coerce_value_to_type(
            ctx,
            ptr,
            ctx.local_runtime_types[dest.index()],
        ));
    }
    let pointer_leaf_infos = ctx.body.local(dest).pointer_leaf_infos.clone();
    let object_ty = ctx
        .type_lowerer()
        .fe_object_ty_to_sonatina_with_pointer_leaf_infos(alloc_ty, &pointer_leaf_infos)
        .unwrap_or_else(|| ctx.fb.declare_array_type(Type::I8, size_bytes));

    Ok(emit_obj_alloc_ref(ctx.fb, object_ty, ctx.is))
}

fn lower_store_inst<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    value: mir::ValueId,
) -> Result<(), LowerError> {
    let value_data = ctx
        .body
        .values
        .get(value.index())
        .ok_or_else(|| LowerError::Internal(format!("unknown value: {value:?}")))?;
    let value_ty = value_data.ty;
    if is_erased_runtime_ty(ctx.db, ctx.target_layout, value_ty) {
        return Ok(());
    }
    if split_place_discriminant_tail(place).is_some()
        && let mir::ValueOrigin::Synthetic(SyntheticValue::Int(value)) = &value_data.origin
        && let Ok(variant_idx) = usize::try_from(value)
        && lower_enum_discriminant_store(ctx, place, variant_idx)?
    {
        return Ok(());
    }

    if value_data.repr.is_ref() {
        let src_place = mir::ir::Place::new(value, mir::ir::MirProjectionPath::new());
        deep_copy_from_places(ctx, place, &src_place, value_ty)?;
        return Ok(());
    }

    let val = lower_value(ctx, value)?;
    store_runtime_value_to_place(ctx, place, value_ty, val)
}

fn store_typed_to_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    val: ValueId,
    stored_ty: TyId<'db>,
) -> Result<(), LowerError> {
    store_runtime_value_to_place(ctx, place, stored_ty, val)
}

fn store_runtime_value_to_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    stored_ty: hir::analysis::ty::ty_def::TyId<'db>,
    value: ValueId,
) -> Result<(), LowerError> {
    if is_transparent_field0_place(ctx, place) {
        let base_place = Place::new(place.base, mir::MirProjectionPath::new());
        return store_runtime_value_to_place(ctx, &base_place, stored_ty, value);
    }

    let lowered = lower_place_terminal(ctx, place)?;
    match terminal_address_space(&lowered, place)? {
        AddressSpaceKind::Memory => {
            if let Some(object_ref) = lowered.object_ref() {
                let object_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
                let stored = if object_elem_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
                    coerce_value_to_type(ctx, value, object_elem_ty)
                } else if ctx.fb.type_of(value).is_obj_ref(&ctx.fb.module_builder.ctx) {
                    let value_elem_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(value))?;
                    let loaded = ctx
                        .fb
                        .insert_inst(ObjLoad::new(ctx.is, value), value_elem_ty);
                    coerce_value_to_runtime_ty(ctx, loaded, stored_ty, object_elem_ty)
                } else {
                    coerce_value_to_runtime_ty(ctx, value, stored_ty, object_elem_ty)
                };
                ctx.fb
                    .insert_inst_no_result(ObjStore::new(ctx.is, object_ref, stored));
                return Ok(());
            }
            if layout::is_packed_scalar_array_access(ctx.db, ctx.body, place, stored_ty)
                .map_err(LowerError::Unsupported)?
            {
                let addr = lowered.word_addr(ctx);
                let val = apply_to_word(ctx.fb, ctx.db, value, stored_ty, ctx.is);
                ctx.fb
                    .insert_inst_no_result(EvmMstore8::new(ctx.is, addr, val));
                return Ok(());
            }
            let ptr_addr = terminal_native_memory_ptr(&lowered, place)?;
            let value_ty = ctx.fb.type_of(value);
            if value_ty.is_pointer(&ctx.fb.module_builder.ctx) {
                ctx.fb
                    .insert_inst_no_result(Mstore::new(ctx.is, ptr_addr, value, value_ty));
                return Ok(());
            }

            let val = apply_to_word(ctx.fb, ctx.db, value, stored_ty, ctx.is);
            ctx.fb
                .insert_inst_no_result(Mstore::new(ctx.is, ptr_addr, val, Type::I256));
            Ok(())
        }
        AddressSpaceKind::Storage | AddressSpaceKind::TransientStorage => {
            let raw = coerce_value_to_word(ctx, value);
            let val = apply_to_word(ctx.fb, ctx.db, raw, stored_ty, ctx.is);
            store_word_to_terminal(ctx, place, lowered, val)
        }
        AddressSpaceKind::Calldata => Err(LowerError::Unsupported("store to calldata".to_string())),
        AddressSpaceKind::Code => Err(LowerError::Unsupported(
            "cannot store to code space".to_string(),
        )),
    }
}

fn load_place_runtime<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
    loaded_ty: hir::analysis::ty::ty_def::TyId<'db>,
    expected_runtime_ty: Type,
) -> Result<ValueId, LowerError> {
    if is_erased_runtime_ty(ctx.db, ctx.target_layout, loaded_ty) {
        return Ok(zero_value_for_type(ctx.fb, expected_runtime_ty, ctx.is));
    }
    if let Some(discriminant) = lower_enum_discriminant_load(ctx, place, expected_runtime_ty)? {
        return Ok(discriminant);
    }

    if is_transparent_field0_place(ctx, place) {
        let base = lower_value(ctx, place.base)?;
        if expected_runtime_ty.is_obj_ref(&ctx.fb.module_builder.ctx) {
            return Ok(coerce_value_to_type(ctx, base, expected_runtime_ty));
        }
        if expected_runtime_ty.is_pointer(&ctx.fb.module_builder.ctx) {
            return Ok(coerce_value_to_type(ctx, base, expected_runtime_ty));
        }
        let raw = coerce_value_to_word(ctx, base);
        let loaded = apply_from_word(ctx.fb, ctx.db, raw, loaded_ty, ctx.is);
        return Ok(coerce_value_to_type(ctx, loaded, expected_runtime_ty));
    }

    let packed = layout::is_packed_scalar_array_access(ctx.db, ctx.body, place, loaded_ty)
        .map_err(LowerError::Unsupported)?;
    let lowered = lower_place_terminal(ctx, place)?;
    if let Some(value) = lower_object_ref_terminal_value(ctx, lowered, expected_runtime_ty)? {
        return Ok(value);
    }
    load_from_terminal(ctx, lowered, place, loaded_ty, expected_runtime_ty, packed)
}

fn is_transparent_field0_place<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    place: &Place<'db>,
) -> bool {
    if place.projection.is_empty() {
        return false;
    }

    let Some(base_value) = ctx.body.values.get(place.base.index()) else {
        return false;
    };
    if !matches!(base_value.repr, mir::ValueRepr::Word) {
        return false;
    }

    mir::repr::peel_transparent_field0_projection_path(ctx.db, base_value.ty, &place.projection)
        .is_some()
}

fn deep_copy_from_places<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    dst_place: &Place<'db>,
    src_place: &Place<'db>,
    value_ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Result<(), LowerError> {
    if is_erased_runtime_ty(ctx.db, ctx.target_layout, value_ty) {
        return Ok(());
    }

    if value_ty
        .adt_ref(ctx.db)
        .is_some_and(|adt| matches!(adt, AdtRef::Enum(_)))
    {
        return deep_copy_enum_from_places(ctx, dst_place, src_place, value_ty);
    }

    if mir::repr::pointer_info_for_ty(ctx.db, ctx.core, value_ty, AddressSpaceKind::Memory)
        .is_some()
    {
        let runtime_ty = ctx.runtime_type_for_loaded_place(src_place, value_ty)?;
        let loaded = load_place_runtime(ctx, src_place, value_ty, runtime_ty)?;
        return store_runtime_value_to_place(ctx, dst_place, value_ty, loaded);
    }

    let dst_space = ctx.body.place_address_space(dst_place);
    let src_space = ctx.body.place_address_space(src_place);

    if value_ty.is_array(ctx.db) {
        if dst_space == AddressSpaceKind::Memory
            && src_space == AddressSpaceKind::Code
            && src_place.projection.is_empty()
        {
            let dst_lowered = lower_place_terminal(ctx, dst_place)?;
            let copy_size = if let Some(mir::ValueData {
                origin: mir::ValueOrigin::ConstRegion(region_id),
                ..
            }) = ctx.body.values.get(src_place.base.index())
            {
                Some(ctx.body.const_region(*region_id).bytes.len())
            } else {
                layout::ty_memory_size_in(ctx.db, ctx.target_layout, value_ty)
            };
            if let Some(size) = copy_size
                && size > 0
                && dst_lowered.object_ref().is_none()
            {
                let dst_addr = dst_lowered.word_addr(ctx);
                let src_addr = lower_place_address(ctx, src_place)?;
                let size_val = ctx.fb.make_imm_value(I256::from(size as u64));
                ctx.fb
                    .insert_inst_no_result(EvmCodeCopy::new(ctx.is, dst_addr, src_addr, size_val));
                return Ok(());
            }
        }

        let Some(len) = layout::array_len(ctx.db, value_ty) else {
            return Err(LowerError::Unsupported(
                "array store requires a constant length".into(),
            ));
        };
        let elem_ty = layout::array_elem_ty(ctx.db, value_ty)
            .ok_or_else(|| LowerError::Unsupported("array store requires element type".into()))?;
        for idx in 0..len {
            let dst_elem = extend_place(dst_place, Projection::Index(IndexSource::Constant(idx)));
            let src_elem = extend_place(src_place, Projection::Index(IndexSource::Constant(idx)));
            deep_copy_from_places(ctx, &dst_elem, &src_elem, elem_ty)?;
        }
        return Ok(());
    }

    if value_ty.field_count(ctx.db) > 0 {
        for (field_idx, field_ty) in value_ty.field_types(ctx.db).iter().copied().enumerate() {
            let dst_field = extend_place(dst_place, Projection::Field(field_idx));
            let src_field = extend_place(src_place, Projection::Field(field_idx));
            deep_copy_from_places(ctx, &dst_field, &src_field, field_ty)?;
        }
        return Ok(());
    }

    let loaded = load_place_runtime(
        ctx,
        src_place,
        value_ty,
        types::value_type(ctx.db, value_ty),
    )?;
    store_runtime_value_to_place(ctx, dst_place, value_ty, loaded)
}

fn deep_copy_enum_from_places<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    dst_place: &Place<'db>,
    src_place: &Place<'db>,
    enum_ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Result<(), LowerError> {
    let Some(adt_def) = enum_ty.adt_def(ctx.db) else {
        return Err(LowerError::Unsupported(
            "enum store requires enum adt".into(),
        ));
    };
    let AdtRef::Enum(enm) = adt_def.adt_ref(ctx.db) else {
        return Err(LowerError::Unsupported(
            "enum store requires enum adt".into(),
        ));
    };

    let discr_ty =
        hir::analysis::ty::ty_def::TyId::new(ctx.db, TyData::TyBase(TyBase::Prim(PrimTy::U256)));
    let src_discr_place = extend_place(src_place, Projection::Discriminant);
    let discr_runtime_ty = specialized_enum_tag_runtime_ty_for_place(ctx, src_place)
        .unwrap_or_else(|| {
            let discr_shape = ctx
                .runtime_shape_for_loaded_place(&src_discr_place)
                .unwrap_or(mir::ir::RuntimeShape::Word(
                    mir::repr::runtime_word_kind_for_ty(ctx.db, discr_ty),
                ));
            ctx.runtime_type_for_ty_and_shape(discr_ty, discr_shape, &[])
        });
    let discr = load_place_runtime(ctx, &src_discr_place, discr_ty, discr_runtime_ty)?;

    let origin_block = ctx
        .fb
        .current_block()
        .ok_or_else(|| LowerError::Internal("missing current block".to_string()))?;
    let cont_block = ctx.fb.append_block();

    let variants = adt_def.fields(ctx.db);
    let mut cases: Vec<(ValueId, BlockId)> = Vec::with_capacity(variants.len());
    let mut case_blocks = Vec::with_capacity(variants.len());
    for (idx, _) in variants.iter().enumerate() {
        let case_block = ctx.fb.append_block();
        case_blocks.push(case_block);
        let case_value = ctx.fb.make_imm_value(Immediate::from_i256(
            I256::from(idx as u64),
            discr_runtime_ty,
        ));
        cases.push((case_value, case_block));
    }

    ctx.fb.switch_to_block(origin_block);
    if cases.is_empty() {
        ctx.fb.insert_inst_no_result(Jump::new(ctx.is, cont_block));
    } else {
        let mut compare_blocks = Vec::with_capacity(cases.len().saturating_sub(1));
        for _ in 0..cases.len().saturating_sub(1) {
            compare_blocks.push(ctx.fb.append_block());
        }

        for (case_idx, (case_value, case_dest)) in cases.into_iter().enumerate() {
            if case_idx > 0 {
                ctx.fb.switch_to_block(compare_blocks[case_idx - 1]);
            }

            let else_dest = if case_idx + 1 < compare_blocks.len() + 1 {
                compare_blocks[case_idx]
            } else {
                cont_block
            };
            let cond = ctx
                .fb
                .insert_inst(Eq::new(ctx.is, discr, case_value), Type::I1);
            ctx.fb
                .insert_inst_no_result(Br::new(ctx.is, cond, case_dest, else_dest));
        }
    }

    for (idx, case_block) in case_blocks.into_iter().enumerate() {
        ctx.fb.switch_to_block(case_block);
        let enum_variant = hir::hir_def::EnumVariant::new(enm, idx);
        if !lower_enum_set_tag_for_place(ctx, dst_place, enum_variant)? {
            let dst_discr_place = extend_place(dst_place, Projection::Discriminant);
            let discr_value = ctx.fb.make_imm_value(I256::from(idx as u64));
            store_typed_to_place(ctx, &dst_discr_place, discr_value, discr_ty)?;
        }
        let ctor = ConstructorKind::Variant(enum_variant, enum_ty);
        for (field_idx, field_ty) in ctor.field_types(ctx.db).iter().copied().enumerate() {
            let proj = Projection::VariantField {
                variant: enum_variant,
                enum_ty,
                field_idx,
            };
            let dst_field = extend_place(dst_place, proj.clone());
            let src_field = extend_place(src_place, proj);
            deep_copy_from_places(ctx, &dst_field, &src_field, field_ty)?;
        }
        ctx.fb.insert_inst_no_result(Jump::new(ctx.is, cont_block));
    }

    ctx.fb.switch_to_block(cont_block);
    Ok(())
}

fn extend_place<'db>(place: &Place<'db>, proj: mir::ir::MirProjection<'db>) -> Place<'db> {
    let mut path = place.projection.clone();
    path.push(proj);
    Place::new(place.base, path)
}

fn condition_to_i1<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    cond: ValueId,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let cond_ty = fb.type_of(cond);
    if cond_ty == Type::I1 {
        cond
    } else {
        let zero = types::zero_value(fb, cond_ty);
        fb.insert_inst(Ne::new(is, cond, zero), Type::I1)
    }
}

fn emit_evm_malloc_ptr<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    size: ValueId,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ptr_ty = fb.ptr_type(Type::I8);
    fb.insert_inst(EvmMalloc::new(is, size), ptr_ty)
}

fn emit_evm_malloc_word_addr<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    size: ValueId,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ptr = emit_evm_malloc_ptr(fb, size, is);
    fb.insert_inst(PtrToInt::new(is, ptr, Type::I256), Type::I256)
}

fn emit_alloca_word_addr<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    alloca_ty: Type,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ptr = emit_alloca_ptr(fb, alloca_ty, is);
    fb.insert_inst(PtrToInt::new(is, ptr, Type::I256), Type::I256)
}

fn emit_obj_alloc_ref<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    object_ty: Type,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let object_ref_ty = fb.module_builder.objref_type(object_ty);
    fb.insert_inst(ObjAlloc::new(is, object_ty), object_ref_ty)
}

fn ensure_const_data_global<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    data: &[u8],
) -> GlobalVariableRef {
    if let Some(&existing) = ctx.const_data_globals.get(data) {
        return existing;
    }

    let elems: Vec<GvInitializer> = data
        .iter()
        .map(|&b| GvInitializer::make_imm(Immediate::I8(b as i8)))
        .collect();
    let array_init = GvInitializer::make_array(elems);
    let label = format!("__fe_const_data_{}", *ctx.data_global_counter);
    *ctx.data_global_counter += 1;
    let array_ty = ctx
        .fb
        .module_builder
        .declare_array_type(Type::I8, data.len());
    let gv_data = GlobalVariableData::constant(label, array_ty, Linkage::Private, array_init);
    let gv_ref = ctx.fb.module_builder.declare_gv(gv_data);
    ctx.const_data_globals.insert(data.to_vec(), gv_ref);
    ctx.data_globals.push(gv_ref);
    gv_ref
}

/// Lower a `ConstAggregate` by registering a global data section and using CODECOPY.
///
/// Registers the constant bytes as a Sonatina global variable (data section),
/// then emits: malloc -> symaddr -> symsize -> codecopy. This is the Sonatina
/// equivalent of Yul's datacopy/dataoffset/datasize pattern.
fn lower_const_aggregate<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    dest: mir::LocalId,
    ty: TyId<'db>,
    data: &[u8],
) -> Result<ValueId, LowerError> {
    if ctx.local_runtime_types[dest.index()].is_obj_ref(&ctx.fb.module_builder.ctx) {
        let size_bytes = layout::ty_memory_size_or_word_in(ctx.db, ctx.target_layout, ty)
            .ok_or_else(|| {
                LowerError::Unsupported(format!(
                    "cannot determine allocation size for `{}`",
                    ty.pretty_print(ctx.db)
                ))
            })?;
        if size_bytes == 0 {
            return Ok(zero_value_for_type(
                ctx.fb,
                ctx.local_runtime_types[dest.index()],
                ctx.is,
            ));
        }
        let pointer_leaf_infos = ctx.body.local(dest).pointer_leaf_infos.clone();
        let object_ty = ctx
            .type_lowerer()
            .fe_object_ty_to_sonatina_with_pointer_leaf_infos(ty, &pointer_leaf_infos)
            .unwrap_or_else(|| ctx.fb.declare_array_type(Type::I8, size_bytes));
        if const_aggregate_object_copy_compatible(ctx.db, ctx.core, ty) {
            let gv_ref = ensure_const_data_global(ctx, data);
            let object_ref = emit_obj_alloc_ref(ctx.fb, object_ty, ctx.is);
            let object_ptr_ty = ctx.fb.ptr_type(object_ty);
            let object_ptr = ctx
                .fb
                .insert_inst(ObjMaterializeStack::new(ctx.is, object_ref), object_ptr_ty);
            let sym = SymbolRef::Global(gv_ref);
            let code_offset = ctx
                .fb
                .insert_inst(SymAddr::new(ctx.is, sym.clone()), Type::I256);
            let code_size = ctx.fb.insert_inst(SymSize::new(ctx.is, sym), Type::I256);
            let dst = coerce_value_to_word(ctx, object_ptr);
            ctx.fb
                .insert_inst_no_result(EvmCodeCopy::new(ctx.is, dst, code_offset, code_size));
            return Ok(object_ref);
        }

        let object_ref = emit_obj_alloc_ref(ctx.fb, object_ty, ctx.is);
        init_const_array_object(ctx, object_ref, ty, data)?;
        return Ok(object_ref);
    }

    let gv_ref = ensure_const_data_global(ctx, data);
    let size_val = ctx.fb.make_imm_value(I256::from(data.len() as u64));
    let ptr = emit_evm_malloc_ptr(ctx.fb, size_val, ctx.is);
    let sym = SymbolRef::Global(gv_ref);
    let code_offset = ctx
        .fb
        .insert_inst(SymAddr::new(ctx.is, sym.clone()), Type::I256);
    let code_size = ctx.fb.insert_inst(SymSize::new(ctx.is, sym), Type::I256);
    let dst = coerce_value_to_word(ctx, ptr);
    ctx.fb
        .insert_inst_no_result(EvmCodeCopy::new(ctx.is, dst, code_offset, code_size));

    Ok(ptr)
}

fn init_const_array_object<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    object_ref: ValueId,
    array_ty: TyId<'db>,
    data: &[u8],
) -> Result<(), LowerError> {
    let Some(len) = layout::array_len(ctx.db, array_ty) else {
        return Err(LowerError::Unsupported(
            "ConstAggregate object lowering requires a fixed-size array".to_string(),
        ));
    };
    let elem_ty = layout::array_elem_ty(ctx.db, array_ty).ok_or_else(|| {
        LowerError::Unsupported(
            "ConstAggregate object lowering requires an array element type".to_string(),
        )
    })?;
    let stride = layout::array_elem_stride_memory_in(ctx.db, ctx.target_layout, array_ty)
        .ok_or_else(|| {
            LowerError::Unsupported(
                "ConstAggregate object lowering requires a constant memory stride".to_string(),
            )
        })?;

    for idx in 0..len {
        let start = idx * stride;
        let end = start + stride;
        let elem_data = data.get(start..end).ok_or_else(|| {
            LowerError::Internal("ConstAggregate payload does not match array layout".to_string())
        })?;
        let idx_val = ctx.fb.make_imm_value(I256::from(idx as u64));
        let array_object_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(object_ref))?;
        let elem_object_ty = if let Ok(ty) = sonatina_array_elem_ty(ctx, array_object_ty) {
            ty
        } else if matches!(
            mir::repr::repr_kind_for_ty(ctx.db, ctx.core, elem_ty),
            mir::repr::ReprKind::Ref
        ) {
            let size = layout::ty_memory_size_or_word_in(ctx.db, ctx.target_layout, elem_ty)
                .ok_or_else(|| {
                    LowerError::Unsupported(format!(
                        "cannot determine allocation size for `{}`",
                        elem_ty.pretty_print(ctx.db)
                    ))
                })?;
            ctx.fb.declare_array_type(Type::I8, size)
        } else {
            types::value_type(ctx.db, elem_ty)
        };
        let elem_ref_ty = ctx.fb.module_builder.objref_type(elem_object_ty);
        let elem_ref = ctx
            .fb
            .insert_inst(ObjIndex::new(ctx.is, object_ref, idx_val), elem_ref_ty);
        if matches!(
            mir::repr::repr_kind_for_ty(ctx.db, ctx.core, elem_ty),
            mir::repr::ReprKind::Ref
        ) {
            init_const_array_object(ctx, elem_ref, elem_ty, elem_data)?;
            continue;
        }

        let elem_value_ty = object_ref_elem_ty(ctx, ctx.fb.type_of(elem_ref))?;
        let elem_value = ctx.fb.make_imm_value(Immediate::from_i256(
            bytes_to_i256(elem_data),
            elem_value_ty,
        ));
        ctx.fb
            .insert_inst_no_result(ObjStore::new(ctx.is, elem_ref, elem_value));
    }

    Ok(())
}

fn emit_alloca_ptr<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    alloca_ty: Type,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
) -> ValueId {
    let ptr_ty = fb.ptr_type(alloca_ty);
    fb.insert_inst(Alloca::new(is, alloca_ty), ptr_ty)
}

fn coerce_value_to_word<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value: ValueId,
) -> ValueId {
    if ctx.fb.type_of(value).is_obj_ref(&ctx.fb.module_builder.ctx) {
        panic!("cannot coerce object refs to raw words");
    }
    if ctx.fb.type_of(value).is_pointer(&ctx.fb.module_builder.ctx) {
        return ctx
            .fb
            .insert_inst(PtrToInt::new(ctx.is, value, Type::I256), Type::I256);
    }

    value
}

fn coerce_value_to_type<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value: ValueId,
    expected_ty: Type,
) -> ValueId {
    let actual_ty = ctx.fb.type_of(value);
    if actual_ty == expected_ty {
        return value;
    }
    if actual_ty.is_obj_ref(&ctx.fb.module_builder.ctx)
        || expected_ty.is_obj_ref(&ctx.fb.module_builder.ctx)
    {
        let actual_cmpd = actual_ty.resolve_compound(&ctx.fb.module_builder.ctx);
        let expected_cmpd = expected_ty.resolve_compound(&ctx.fb.module_builder.ctx);
        assert_eq!(
            actual_ty, expected_ty,
            "cannot coerce object reference value from {actual_ty:?} {actual_cmpd:?} to {expected_ty:?} {expected_cmpd:?}"
        );
        return value;
    }

    let actual_is_ptr = actual_ty.is_pointer(&ctx.fb.module_builder.ctx);
    let expected_is_ptr = expected_ty.is_pointer(&ctx.fb.module_builder.ctx);
    match (actual_is_ptr, expected_is_ptr) {
        (true, false) => ctx
            .fb
            .insert_inst(PtrToInt::new(ctx.is, value, expected_ty), expected_ty),
        (false, true) => coerce_word_addr_to_ptr(ctx, value, expected_ty),
        (true, true) => bitcast_ptr(ctx, value, expected_ty),
        (false, false) => value,
    }
}

fn coerce_value_to_runtime_ty<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value: ValueId,
    value_ty: TyId<'db>,
    expected_ty: Type,
) -> ValueId {
    let actual_ty = ctx.fb.type_of(value);
    if actual_ty.is_obj_ref(&ctx.fb.module_builder.ctx)
        || expected_ty.is_obj_ref(&ctx.fb.module_builder.ctx)
    {
        return coerce_value_to_type(ctx, value, expected_ty);
    }
    let actual_is_ptr = actual_ty.is_pointer(&ctx.fb.module_builder.ctx);
    let expected_is_ptr = expected_ty.is_pointer(&ctx.fb.module_builder.ctx);
    if actual_is_ptr || expected_is_ptr {
        return coerce_value_to_type(ctx, value, expected_ty);
    }

    coerce_runtime_value(ctx.fb, ctx.db, value, value_ty, expected_ty, ctx.is)
}

fn coerce_word_addr_to_ptr<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    addr: ValueId,
    ptr_ty: Type,
) -> ValueId {
    if ctx.fb.type_of(addr).is_pointer(&ctx.fb.module_builder.ctx) {
        return bitcast_ptr(ctx, addr, ptr_ty);
    }

    if let Some(from_ptr) = ptr_source_from_word_addr(ctx, addr) {
        return bitcast_ptr(ctx, from_ptr, ptr_ty);
    }

    ctx.fb
        .insert_inst(IntToPtr::new(ctx.is, addr, ptr_ty), ptr_ty)
}

fn ptr_source_from_word_addr<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    value: ValueId,
) -> Option<ValueId> {
    let Value::Inst { inst, .. } = ctx.fb.func.dfg.value(value) else {
        return None;
    };
    let ptr_to_int = sonatina_ir::inst::downcast::<&PtrToInt>(ctx.is, ctx.fb.func.dfg.inst(*inst))?;
    Some(*ptr_to_int.from())
}

fn bitcast_ptr<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    ptr: ValueId,
    ptr_ty: Type,
) -> ValueId {
    if ctx.fb.type_of(ptr) == ptr_ty {
        return ptr;
    }
    ctx.fb
        .insert_inst(Bitcast::new(ctx.is, ptr, ptr_ty), ptr_ty)
}

/// Returns (or lazily creates) a revert block that emits `Panic(uint256)` with the given code.
fn ensure_panic_revert_block<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    panic_code: u64,
) -> Result<BlockId, LowerError> {
    if let Some(&block) = ctx.panic_revert_blocks.get(&panic_code) {
        return Ok(block);
    }

    let origin_block = ctx
        .fb
        .current_block()
        .ok_or_else(|| LowerError::Internal("missing current block".to_string()))?;
    let revert_block = ctx.fb.append_block();
    ctx.fb.switch_to_block(revert_block);

    // Emit Panic(uint256) revert payload.
    // Layout at memory offset 0: [selector 4 bytes][uint256 code 32 bytes] = 36 bytes.
    let selector_val = ctx
        .fb
        .make_imm_value(I256::from_be_bytes(&PANIC_SELECTOR_WORD));
    let zero = ctx.fb.make_imm_value(I256::zero());
    ctx.fb
        .insert_inst_no_result(Mstore::new(ctx.is, zero, selector_val, Type::I256));
    let four = ctx.fb.make_imm_value(I256::from(4u64));
    let code_val = ctx.fb.make_imm_value(I256::from(panic_code));
    ctx.fb
        .insert_inst_no_result(Mstore::new(ctx.is, four, code_val, Type::I256));
    let thirty_six = ctx.fb.make_imm_value(I256::from(36u64));
    ctx.fb
        .insert_inst_no_result(EvmRevert::new(ctx.is, zero, thirty_six));

    ctx.fb.switch_to_block(origin_block);
    ctx.panic_revert_blocks.insert(panic_code, revert_block);
    Ok(revert_block)
}

/// Emit a conditional branch to a Panic revert block if `overflow_flag` (I1) is true.
fn emit_panic_revert<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    overflow_flag: ValueId,
    panic_code: u64,
) -> Result<(), LowerError> {
    let revert_block = ensure_panic_revert_block(ctx, panic_code)?;
    let continue_block = ctx.fb.append_block();
    ctx.fb
        .insert_inst_no_result(Br::new(ctx.is, overflow_flag, revert_block, continue_block));
    ctx.fb.switch_to_block(continue_block);
    Ok(())
}

fn try_lower_generic_saturating_intrinsic<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    call: &mir::CallOrigin<'db>,
) -> Result<Option<ValueId>, LowerError> {
    let Some(mir::ir::CallTargetRef::Hir(target)) = call.target.as_ref() else {
        return Ok(None);
    };
    match target.callable_def.ingot(ctx.db).kind(ctx.db) {
        IngotKind::Core | IngotKind::Std => {}
        _ => return Ok(None),
    }

    let hir::hir_def::CallableDef::Func(func) = target.callable_def else {
        return Ok(None);
    };
    if func.body(ctx.db).is_some() {
        return Ok(None);
    }

    let Some(name) = target.callable_def.name(ctx.db) else {
        return Ok(None);
    };
    let name = name.data(ctx.db).as_str();
    if !matches!(
        name,
        "__saturating_add" | "__saturating_sub" | "__saturating_mul"
    ) {
        return Ok(None);
    }
    if !call.effect_args.is_empty() {
        return Err(LowerError::Internal(format!(
            "saturating intrinsic call unexpectedly has effect args: {name}"
        )));
    }

    let [ty] = target.generic_args.as_slice() else {
        return Err(LowerError::Internal(format!(
            "saturating intrinsic `{name}` must have exactly one type argument"
        )));
    };
    let base_ty = ty.base_ty(ctx.db);
    let TyData::TyBase(TyBase::Prim(prim)) = base_ty.data(ctx.db) else {
        return Err(LowerError::Internal(format!(
            "saturating intrinsic `{name}` type must be primitive integral, got `{}`",
            ty.pretty_print(ctx.db)
        )));
    };
    if !prim.is_integral() {
        return Err(LowerError::Internal(format!(
            "saturating intrinsic `{name}` type must be integral, got `{}`",
            ty.pretty_print(ctx.db)
        )));
    }

    let op_ty = checked_intrinsic_value_type(*prim)?;
    let signed = prim_is_signed(*prim);
    let [a, b] = call.args.as_slice() else {
        return Err(LowerError::Internal(format!(
            "saturating intrinsic `{name}` expects 2 arguments, got {}",
            call.args.len()
        )));
    };
    let lhs_word = lower_value(ctx, *a)?;
    let rhs_word = lower_value(ctx, *b)?;
    let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
    let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
    let result = match (name, signed) {
        ("__saturating_add", true) => ctx.fb.insert_saddsat(lhs, rhs),
        ("__saturating_add", false) => ctx.fb.insert_uaddsat(lhs, rhs),
        ("__saturating_sub", true) => ctx.fb.insert_ssubsat(lhs, rhs),
        ("__saturating_sub", false) => ctx.fb.insert_usubsat(lhs, rhs),
        ("__saturating_mul", true) => ctx.fb.insert_smulsat(lhs, rhs),
        ("__saturating_mul", false) => ctx.fb.insert_umulsat(lhs, rhs),
        _ => unreachable!(),
    };
    Ok(Some(result))
}

fn checked_intrinsic_prim<'db>(
    db: &'db DriverDataBase,
    ty: hir::analysis::ty::ty_def::TyId<'db>,
) -> Result<PrimTy, LowerError> {
    let base_ty = ty.base_ty(db);
    let TyData::TyBase(TyBase::Prim(prim)) = base_ty.data(db) else {
        return Err(LowerError::Internal(format!(
            "checked intrinsic type must be a primitive integer, got `{}`",
            ty.pretty_print(db)
        )));
    };
    if !prim.is_integral() {
        return Err(LowerError::Internal(format!(
            "checked intrinsic type must be integral, got `{}`",
            ty.pretty_print(db)
        )));
    }
    Ok(*prim)
}

fn checked_intrinsic_value_type(prim: PrimTy) -> Result<Type, LowerError> {
    types::prim_scalar_type(prim).ok_or_else(|| {
        LowerError::Internal(format!(
            "checked intrinsic type must be integral, got `{prim:?}`"
        ))
    })
}

fn lower_checked_operand<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
    value: ValueId,
    op_ty: Type,
    signed: bool,
) -> ValueId {
    cast_int_value(fb, is, value, op_ty, signed)
}

fn lower_checked_intrinsic<'db, C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, 'db, C>,
    checked: CheckedIntrinsic<'db>,
    args: &[mir::ir::ValueId],
) -> Result<ValueId, LowerError> {
    let prim = checked_intrinsic_prim(ctx.db, checked.ty)?;
    let op_ty = checked_intrinsic_value_type(prim)?;
    let signed = prim_is_signed(prim);

    match checked.op {
        CheckedArithmeticOp::Add => {
            let [a, b] = args else {
                return Err(LowerError::Internal(format!(
                    "checked add expects 2 arguments, got {}",
                    args.len()
                )));
            };
            let lhs_word = lower_value(ctx, *a)?;
            let rhs_word = lower_value(ctx, *b)?;
            let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
            let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
            let [raw, overflow] = if signed {
                ctx.fb.insert_saddo(lhs, rhs)
            } else {
                ctx.fb.insert_uaddo(lhs, rhs)
            };
            emit_panic_revert(ctx, overflow, PANIC_CODE_OVERFLOW)?;
            Ok(raw)
        }
        CheckedArithmeticOp::Sub => {
            let [a, b] = args else {
                return Err(LowerError::Internal(format!(
                    "checked sub expects 2 arguments, got {}",
                    args.len()
                )));
            };
            let lhs_word = lower_value(ctx, *a)?;
            let rhs_word = lower_value(ctx, *b)?;
            let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
            let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
            let [raw, overflow] = if signed {
                ctx.fb.insert_ssubo(lhs, rhs)
            } else {
                ctx.fb.insert_usubo(lhs, rhs)
            };
            emit_panic_revert(ctx, overflow, PANIC_CODE_OVERFLOW)?;
            Ok(raw)
        }
        CheckedArithmeticOp::Mul => {
            let [a, b] = args else {
                return Err(LowerError::Internal(format!(
                    "checked mul expects 2 arguments, got {}",
                    args.len()
                )));
            };
            let lhs_word = lower_value(ctx, *a)?;
            let rhs_word = lower_value(ctx, *b)?;
            let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
            let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
            let [raw, overflow] = if signed {
                ctx.fb.insert_smulo(lhs, rhs)
            } else {
                ctx.fb.insert_umulo(lhs, rhs)
            };
            emit_panic_revert(ctx, overflow, PANIC_CODE_OVERFLOW)?;
            Ok(raw)
        }
        CheckedArithmeticOp::Div => {
            let [a, b] = args else {
                return Err(LowerError::Internal(format!(
                    "checked div expects 2 arguments, got {}",
                    args.len()
                )));
            };
            let lhs_word = lower_value(ctx, *a)?;
            let rhs_word = lower_value(ctx, *b)?;
            let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
            let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
            let [raw, overflow] = if signed {
                let [raw, overflow] = ctx.fb.insert_evm_sdivo(lhs, rhs);
                let zero = ctx.fb.make_imm_value(I256::zero());
                let div_by_zero = ctx.fb.insert_inst(Eq::new(ctx.is, rhs, zero), Type::I1);
                emit_panic_revert(ctx, div_by_zero, PANIC_CODE_DIVISION_BY_ZERO)?;
                [raw, overflow]
            } else {
                ctx.fb.insert_evm_udivo(lhs, rhs)
            };
            let panic_code = if signed {
                PANIC_CODE_OVERFLOW
            } else {
                PANIC_CODE_DIVISION_BY_ZERO
            };
            emit_panic_revert(ctx, overflow, panic_code)?;
            Ok(raw)
        }
        CheckedArithmeticOp::Rem => {
            let [a, b] = args else {
                return Err(LowerError::Internal(format!(
                    "checked rem expects 2 arguments, got {}",
                    args.len()
                )));
            };
            let lhs_word = lower_value(ctx, *a)?;
            let rhs_word = lower_value(ctx, *b)?;
            let lhs = lower_checked_operand(ctx.fb, ctx.is, lhs_word, op_ty, signed);
            let rhs = lower_checked_operand(ctx.fb, ctx.is, rhs_word, op_ty, signed);
            let [raw, overflow] = if signed {
                ctx.fb.insert_evm_smodo(lhs, rhs)
            } else {
                ctx.fb.insert_evm_umodo(lhs, rhs)
            };
            emit_panic_revert(ctx, overflow, PANIC_CODE_DIVISION_BY_ZERO)?;
            Ok(raw)
        }
        CheckedArithmeticOp::Neg => {
            let [arg] = args else {
                return Err(LowerError::Internal(format!(
                    "checked neg expects 1 argument, got {}",
                    args.len()
                )));
            };
            if !signed {
                return Err(LowerError::Internal(format!(
                    "checked neg is not defined for unsigned type `{}`",
                    checked.ty.pretty_print(ctx.db)
                )));
            }
            let val_word = lower_value(ctx, *arg)?;
            let val = lower_checked_operand(ctx.fb, ctx.is, val_word, op_ty, true);
            let [raw, overflow] = ctx.fb.insert_snego(val);
            emit_panic_revert(ctx, overflow, PANIC_CODE_OVERFLOW)?;
            Ok(raw)
        }
    }
}

/// Maps a raw core intrinsic suffix to the primitive type it operates on.
const INTRINSIC_SUFFIX_TYPES: &[(&str, PrimTy)] = &[
    ("_u8", PrimTy::U8),
    ("_u16", PrimTy::U16),
    ("_u32", PrimTy::U32),
    ("_u64", PrimTy::U64),
    ("_u128", PrimTy::U128),
    ("_u256", PrimTy::U256),
    ("_usize", PrimTy::Usize),
    ("_i8", PrimTy::I8),
    ("_i16", PrimTy::I16),
    ("_i32", PrimTy::I32),
    ("_i64", PrimTy::I64),
    ("_i128", PrimTy::I128),
    ("_i256", PrimTy::I256),
    ("_isize", PrimTy::Isize),
    ("_bool", PrimTy::Bool),
];

fn intrinsic_name_parts(callee_name: &str) -> Option<(&str, PrimTy)> {
    INTRINSIC_SUFFIX_TYPES.iter().find_map(|(suffix, prim)| {
        callee_name
            .strip_suffix(suffix)
            .and_then(|prefix| prefix.strip_prefix("__"))
            .map(|op| (op, *prim))
    })
}

fn intrinsic_value_type(prim: PrimTy) -> Type {
    types::prim_scalar_type(prim).unwrap_or(Type::I256)
}

fn lower_intrinsic_operand<C: sonatina_ir::func_cursor::FuncCursor>(
    fb: &mut sonatina_ir::builder::FunctionBuilder<C>,
    is: &sonatina_ir::inst::evm::inst_set::EvmInstSet,
    value: ValueId,
    prim: PrimTy,
    op_ty: Type,
) -> ValueId {
    if prim == PrimTy::Bool {
        condition_to_i1(fb, value, is)
    } else {
        cast_int_value(fb, is, value, op_ty, prim_is_signed(prim))
    }
}

/// Try to lower a `__<op>_<type>` core numeric intrinsic to native Sonatina
/// instructions. Returns `Ok(Some(value))` if the intrinsic was handled,
/// `Ok(None)` if the callee name is not a recognized intrinsic.
fn try_lower_numeric_intrinsic<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    callee_name: &str,
    args: &[mir::ir::ValueId],
) -> Result<Option<ValueId>, LowerError> {
    if !callee_name.starts_with("__") {
        return Ok(None);
    }

    // Strip the type suffix to get the operation name.
    let Some((op, prim)) = intrinsic_name_parts(callee_name) else {
        return Ok(None);
    };
    let op_ty = intrinsic_value_type(prim);
    let signed = prim_is_signed(prim);

    if op.starts_with("checked_") {
        return Err(LowerError::Internal(format!(
            "checked arithmetic intrinsic `{callee_name}` must be lowered via typed checked metadata"
        )));
    }

    match op {
        // Emit Sonatina ops at the intrinsic's actual width and let the EVM
        // legalizer normalize masks/sign extension for sub-word integers.
        "lt" | "gt" | "eq" | "ne" | "le" | "ge" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let cmp = match op {
                "lt" => {
                    if signed {
                        ctx.fb.insert_inst(Slt::new(ctx.is, lhs, rhs), Type::I1)
                    } else {
                        ctx.fb.insert_inst(Lt::new(ctx.is, lhs, rhs), Type::I1)
                    }
                }
                "gt" => {
                    if signed {
                        ctx.fb.insert_inst(Slt::new(ctx.is, rhs, lhs), Type::I1)
                    } else {
                        ctx.fb.insert_inst(Gt::new(ctx.is, lhs, rhs), Type::I1)
                    }
                }
                "eq" => ctx.fb.insert_inst(Eq::new(ctx.is, lhs, rhs), Type::I1),
                "ne" => {
                    let eq = ctx.fb.insert_inst(Eq::new(ctx.is, lhs, rhs), Type::I1);
                    ctx.fb.insert_inst(IsZero::new(ctx.is, eq), Type::I1)
                }
                "le" => {
                    let gt = if signed {
                        ctx.fb.insert_inst(Slt::new(ctx.is, rhs, lhs), Type::I1)
                    } else {
                        ctx.fb.insert_inst(Gt::new(ctx.is, lhs, rhs), Type::I1)
                    };
                    ctx.fb.insert_inst(IsZero::new(ctx.is, gt), Type::I1)
                }
                "ge" => {
                    let lt = if signed {
                        ctx.fb.insert_inst(Slt::new(ctx.is, lhs, rhs), Type::I1)
                    } else {
                        ctx.fb.insert_inst(Lt::new(ctx.is, lhs, rhs), Type::I1)
                    };
                    ctx.fb.insert_inst(IsZero::new(ctx.is, lt), Type::I1)
                }
                _ => unreachable!(),
            };
            Ok(Some(cmp))
        }

        "add" | "sub" | "mul" | "pow" | "shl" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let raw = match op {
                "add" => ctx.fb.insert_inst(Add::new(ctx.is, lhs, rhs), op_ty),
                "sub" => ctx.fb.insert_inst(Sub::new(ctx.is, lhs, rhs), op_ty),
                "mul" => ctx.fb.insert_inst(Mul::new(ctx.is, lhs, rhs), op_ty),
                "pow" => ctx.fb.insert_inst(EvmExp::new(ctx.is, lhs, rhs), op_ty),
                "shl" => ctx.fb.insert_inst(Shl::new(ctx.is, rhs, lhs), op_ty),
                _ => unreachable!(),
            };
            Ok(Some(raw))
        }
        "div" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let [raw, _overflow] = if signed {
                ctx.fb.insert_evm_sdivo(lhs, rhs)
            } else {
                ctx.fb.insert_evm_udivo(lhs, rhs)
            };
            Ok(Some(raw))
        }
        "rem" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let [raw, _overflow] = if signed {
                ctx.fb.insert_evm_smodo(lhs, rhs)
            } else {
                ctx.fb.insert_evm_umodo(lhs, rhs)
            };
            Ok(Some(raw))
        }
        "shr" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let raw = if signed {
                ctx.fb.insert_inst(Sar::new(ctx.is, rhs, lhs), op_ty)
            } else {
                ctx.fb.insert_inst(Shr::new(ctx.is, rhs, lhs), op_ty)
            };
            Ok(Some(raw))
        }

        "bitand" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let raw = ctx.fb.insert_inst(And::new(ctx.is, lhs, rhs), op_ty);
            Ok(Some(raw))
        }
        "bitor" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let raw = ctx.fb.insert_inst(Or::new(ctx.is, lhs, rhs), op_ty);
            Ok(Some(raw))
        }
        "bitxor" => {
            let (lhs_word, rhs_word) = lower_binary_args(ctx, callee_name, args)?;
            let lhs = lower_intrinsic_operand(ctx.fb, ctx.is, lhs_word, prim, op_ty);
            let rhs = lower_intrinsic_operand(ctx.fb, ctx.is, rhs_word, prim, op_ty);
            let raw = ctx.fb.insert_inst(Xor::new(ctx.is, lhs, rhs), op_ty);
            Ok(Some(raw))
        }

        "bitnot" => {
            let val_word = lower_unary_arg(ctx, callee_name, args)?;
            let val = lower_intrinsic_operand(ctx.fb, ctx.is, val_word, prim, op_ty);
            let raw = ctx.fb.insert_inst(Not::new(ctx.is, val), op_ty);
            Ok(Some(raw))
        }
        "not" => {
            if prim != PrimTy::Bool {
                return Err(LowerError::Internal(format!(
                    "logical not intrinsic must be bool-typed, got `{callee_name}`"
                )));
            }
            let val_word = lower_unary_arg(ctx, callee_name, args)?;
            let val = lower_intrinsic_operand(ctx.fb, ctx.is, val_word, prim, op_ty);
            let is_zero = ctx.fb.insert_inst(IsZero::new(ctx.is, val), Type::I1);
            Ok(Some(is_zero))
        }
        "neg" => {
            let val_word = lower_unary_arg(ctx, callee_name, args)?;
            let val = lower_intrinsic_operand(ctx.fb, ctx.is, val_word, prim, op_ty);
            let raw = ctx.fb.insert_inst(Neg::new(ctx.is, val), op_ty);
            Ok(Some(raw))
        }

        // Not a recognized intrinsic operation.
        _ => Ok(None),
    }
}

fn lower_binary_args<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    callee_name: &str,
    args: &[mir::ir::ValueId],
) -> Result<(ValueId, ValueId), LowerError> {
    let [a, b] = args else {
        return Err(LowerError::Internal(format!(
            "{callee_name} requires 2 arguments"
        )));
    };
    let lhs = lower_value(ctx, *a)?;
    let rhs = lower_value(ctx, *b)?;
    Ok((lhs, rhs))
}

fn lower_unary_arg<C: sonatina_ir::func_cursor::FuncCursor>(
    ctx: &mut LowerCtx<'_, '_, C>,
    callee_name: &str,
    args: &[mir::ir::ValueId],
) -> Result<ValueId, LowerError> {
    let [a] = args else {
        return Err(LowerError::Internal(format!(
            "{callee_name} requires 1 argument"
        )));
    };
    lower_value(ctx, *a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_pointer_leaf_info_normalizes_root_entries() {
        let pointer_leaf_infos = vec![
            (
                mir::MirProjectionPath::new(),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: None,
                },
            ),
            (
                mir::MirProjectionPath::new(),
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            ),
        ];

        assert_eq!(
            root_pointer_leaf_info(&pointer_leaf_infos),
            Some(PointerInfo {
                address_space: AddressSpaceKind::Storage,
                target_ty: None,
            }),
        );
    }

    #[test]
    fn array_elem_pointer_leaf_infos_preserve_dynamic_index_entries() {
        let pointer_leaf_infos = vec![
            (
                mir::MirProjectionPath::from_projection(Projection::Index(IndexSource::Constant(
                    0,
                ))),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: None,
                },
            ),
            (
                mir::MirProjectionPath::from_projection(Projection::Index(IndexSource::Dynamic(
                    mir::ValueId(7),
                ))),
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            ),
            (
                mir::MirProjectionPath::from_projection(Projection::Field(0)),
                PointerInfo {
                    address_space: AddressSpaceKind::Calldata,
                    target_ty: None,
                },
            ),
        ];

        assert_eq!(
            array_elem_pointer_leaf_infos(&pointer_leaf_infos),
            vec![(
                mir::MirProjectionPath::new(),
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            )],
        );
    }
}
