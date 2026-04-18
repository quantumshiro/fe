//! Type mapping from Fe MIR to Sonatina IR types.

use driver::DriverDataBase;
use hir::analysis::ty::ty_def::{CapabilityKind, PrimTy, TyBase, TyData, TyId};
use mir::{ir::RuntimeWordKind, repr};
use sonatina_ir::{Immediate, Type, ValueId, builder::FunctionBuilder, func_cursor::FuncCursor};

/// Returns the Sonatina scalar type for a Fe primitive, when one exists.
pub fn prim_scalar_type(prim: PrimTy) -> Option<Type> {
    match prim {
        PrimTy::Bool => Some(Type::I1),
        PrimTy::U8 | PrimTy::I8 => Some(Type::I8),
        PrimTy::U16 | PrimTy::I16 => Some(Type::I16),
        PrimTy::U32 | PrimTy::I32 => Some(Type::I32),
        PrimTy::U64 | PrimTy::I64 => Some(Type::I64),
        PrimTy::U128 | PrimTy::I128 => Some(Type::I128),
        PrimTy::U256 | PrimTy::I256 | PrimTy::Usize | PrimTy::Isize => Some(Type::I256),
        PrimTy::String
        | PrimTy::Array
        | PrimTy::Tuple(_)
        | PrimTy::Ptr
        | PrimTy::View
        | PrimTy::BorrowMut
        | PrimTy::BorrowRef => None,
    }
}

/// Returns the Sonatina runtime value type for a Fe scalar-or-pointer runtime value.
pub fn value_type(db: &DriverDataBase, ty: TyId<'_>) -> Type {
    let ty = match ty.as_capability(db) {
        Some((CapabilityKind::View, inner)) => inner,
        _ => ty,
    };
    let leaf_ty = repr::word_conversion_leaf_ty(db, ty);
    if let TyData::TyBase(TyBase::Prim(prim)) = leaf_ty.base_ty(db).data(db)
        && let Some(ty) = prim_scalar_type(*prim)
    {
        return ty;
    }

    Type::I256
}

pub fn runtime_word_type(kind: RuntimeWordKind) -> Type {
    match kind {
        RuntimeWordKind::I1 => Type::I1,
        RuntimeWordKind::I8 => Type::I8,
        RuntimeWordKind::I16 => Type::I16,
        RuntimeWordKind::I32 => Type::I32,
        RuntimeWordKind::I64 => Type::I64,
        RuntimeWordKind::I128 => Type::I128,
        RuntimeWordKind::I256 => Type::I256,
    }
}

/// Creates a zero/undef value of the given Sonatina type.
pub fn zero_value<C: FuncCursor>(fb: &mut FunctionBuilder<C>, ty: Type) -> ValueId {
    if ty == Type::Unit {
        fb.make_undef_value(Type::Unit)
    } else {
        fb.make_imm_value(Immediate::zero(ty))
    }
}
