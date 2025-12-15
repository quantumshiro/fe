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

use crate::analysis::HirAnalysisDb;
use crate::analysis::ty::adt_def::AdtRef;
use crate::analysis::ty::simplified_pattern::ConstructorKind;
use crate::analysis::ty::ty_def::{PrimTy, TyBase, TyData, TyId, prim_int_bits};
use crate::hir_def::EnumVariant;

/// Size of an EVM word in bytes (256 bits).
pub const WORD_SIZE_BYTES: u64 = 32;

/// Size of enum discriminant in bytes.
///
/// All enums use a 256-bit (32-byte) discriminant, matching EVM word size.
pub const DISCRIMINANT_SIZE_BYTES: u64 = WORD_SIZE_BYTES;

/// Computes the byte size of a type.
///
/// Returns `None` for unsupported types (unsized, unresolved, enums).
/// For enum sizes, use [`enum_size_bytes`] which handles discriminant + max payload.
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

/// Like [`ty_size_bytes`], but returns [`WORD_SIZE_BYTES`] for unknown types.
///
/// This encodes Fe's EVM convention: types with unknown size (enums, pointers,
/// unresolved types) are stored as 32-byte words.
pub fn ty_size_bytes_or_word(db: &dyn HirAnalysisDb, ty: TyId<'_>) -> u64 {
    ty_size_bytes(db, ty).unwrap_or(WORD_SIZE_BYTES)
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
    if field_idx >= field_types.len() {
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

    if field_idx >= field_types.len() {
        return None;
    }

    let mut offset = 0u64;
    for field_ty in field_types.iter().take(field_idx) {
        offset += ty_size_bytes(db, *field_ty)?;
    }
    Some(offset)
}

/// Computes the byte size of a variant's payload (sum of field sizes).
///
/// # Returns
/// - `Some(size)` if all field sizes can be computed
/// - `None` if any field has unknown size
pub fn variant_payload_size_bytes(
    db: &dyn HirAnalysisDb,
    enum_ty: TyId<'_>,
    variant: EnumVariant<'_>,
) -> Option<u64> {
    let ctor = ConstructorKind::Variant(variant, enum_ty);
    let field_types = ctor.field_types(db);

    let mut size = 0u64;
    for field_ty in field_types.iter() {
        size += ty_size_bytes(db, *field_ty)?;
    }
    Some(size)
}

/// Computes the total byte size of an enum (discriminant + max payload).
///
/// # Returns
/// - `Some(size)` if all variant payloads can be computed
/// - `None` if any variant has unknown field sizes
pub fn enum_size_bytes(db: &dyn HirAnalysisDb, enum_ty: TyId<'_>) -> Option<u64> {
    let adt_def = enum_ty.adt_def(db)?;
    let AdtRef::Enum(enm) = adt_def.adt_ref(db) else {
        return None;
    };

    let mut max_payload: u64 = 0;
    for variant in enm.variants(db) {
        let ev = EnumVariant::new(enm, variant.idx);
        let payload = variant_payload_size_bytes(db, enum_ty, ev)?;
        max_payload = max_payload.max(payload);
    }

    Some(DISCRIMINANT_SIZE_BYTES + max_payload)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn discriminant_size_is_32_bytes() {
        assert_eq!(DISCRIMINANT_SIZE_BYTES, 32);
    }
}
