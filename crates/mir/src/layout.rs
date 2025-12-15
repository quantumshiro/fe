//! Type layout computation for Fe's memory model.
//!
//! This module provides the canonical source of truth for type sizes and field
//! offsets. Both MIR lowering and codegen should use these functions to ensure
//! consistent layout computation across the compiler.
//!
//! # Memory Model
//!
//! Fe uses a packed byte layout (not Solidity's 32-byte slot per field):
//! - Primitives use their natural byte size (u8 = 1 byte, u256 = 32 bytes)
//! - Structs/tuples pack fields contiguously
//! - Enums have a 32-byte discriminant followed by payload fields

use hir::analysis::ty::adt_def::AdtRef;
use hir::analysis::ty::simplified_pattern::ConstructorKind;
use hir::analysis::ty::ty_def::{PrimTy, TyBase, TyData, TyId, prim_int_bits};
use hir::analysis::HirAnalysisDb;
use hir::hir_def::EnumVariant;

/// Size of enum discriminant in bytes.
///
/// All enums use a 256-bit (32-byte) discriminant, matching EVM word size.
pub const DISCRIMINANT_SIZE_BYTES: u64 = 32;

/// Computes the byte size of a type.
///
/// Returns `None` for types with unknown/dynamic size (e.g., unsized types,
/// unresolved types, enums with variant payloads).
///
/// # Supported Types
/// - Primitives: bool (1), u8-u256/i8-i256 (1-32 bytes)
/// - Tuples: sum of field sizes
/// - Structs: sum of field sizes
pub fn ty_size_bytes(db: &dyn HirAnalysisDb, ty: TyId<'_>) -> Option<u64> {
    // Handle tuples first (check base type for TyApp cases)
    if ty.is_tuple(db) {
        let mut size = 0u64;
        for field_ty in ty.field_types(db) {
            size += ty_size_bytes(db, field_ty)?;
        }
        return Some(size);
    }

    // Handle primitives
    if let TyData::TyBase(TyBase::Prim(prim)) = ty.base_ty(db).data(db) {
        if *prim == PrimTy::Bool {
            return Some(1);
        }
        if let Some(bits) = prim_int_bits(*prim) {
            return Some((bits / 8) as u64);
        }
    }

    // Handle ADT types (structs) - use adt_def() which handles TyApp
    if let Some(adt_def) = ty.adt_def(db)
        && matches!(adt_def.adt_ref(db), AdtRef::Struct(_))
    {
        let mut size = 0u64;
        for field_ty in ty.field_types(db) {
            size += ty_size_bytes(db, field_ty)?;
        }
        return Some(size);
    }

    None
}

/// Computes the byte offset to a field within a struct or tuple.
///
/// The offset is the sum of sizes of all fields before `field_idx`.
///
/// # Returns
/// - `Some(offset)` if the type has fields and offset can be computed
/// - `None` if field_idx is out of bounds or type has no fields
pub fn field_offset_bytes(db: &dyn HirAnalysisDb, ty: TyId<'_>, field_idx: usize) -> Option<u64> {
    let field_types = ty.field_types(db);
    if field_idx > field_types.len() {
        return None;
    }

    let mut offset = 0u64;
    for field_ty in field_types.iter().take(field_idx) {
        offset += ty_size_bytes(db, *field_ty)?;
    }
    Some(offset)
}

/// Computes the byte offset to a field within an enum variant's payload.
///
/// This is the offset **relative to the payload start** (i.e., after the
/// discriminant). To get the absolute offset from the enum base, add
/// `DISCRIMINANT_SIZE_BYTES`.
///
/// # Returns
/// - `Some(offset)` if the variant and field exist
/// - `None` if field_idx is out of bounds or variant has no fields
pub fn variant_field_offset_bytes(
    db: &dyn HirAnalysisDb,
    enum_ty: TyId<'_>,
    variant: EnumVariant<'_>,
    field_idx: usize,
) -> Option<u64> {
    let ctor = ConstructorKind::Variant(variant, enum_ty);
    let field_types = ctor.field_types(db);

    if field_idx > field_types.len() {
        return None;
    }

    let mut offset = 0u64;
    for field_ty in field_types.iter().take(field_idx) {
        offset += ty_size_bytes(db, *field_ty)?;
    }
    Some(offset)
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: Full integration tests require a database with types.
    // These would be added as part of the test suite with fixture types.

    #[test]
    fn discriminant_size_is_32_bytes() {
        assert_eq!(DISCRIMINANT_SIZE_BYTES, 32);
    }
}
