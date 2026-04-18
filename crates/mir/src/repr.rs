//! Runtime representation queries for MIR lowering and codegen.
//!
//! Fe exposes rich structural types (structs/tuples/arrays/enums), but MIR uses a smaller set of
//! runtime representation categories:
//! - word-like values (`ValueRepr::Word`)
//! - opaque pointers (`ValueRepr::Ptr`)
//! - by-reference aggregates (`ValueRepr::Ref`)
//!
//! This module centralizes the logic for computing those representation categories, including
//! recursive elimination of "newtype" wrappers (single-field structs and single-element tuples).
//! Newtypes are treated as transparent wrappers: their runtime representation is the same as their
//! (recursively unwrapped) single field, while preserving the logical type (`TyId`) elsewhere in
//! MIR.

use hir::analysis::HirAnalysisDb;
use hir::analysis::ty::adt_def::AdtRef;
use hir::analysis::ty::normalize::normalize_ty;
use hir::analysis::ty::ty_def::{TyBase, TyData, TyId};
use hir::analysis::ty::{
    corelib::resolve_core_trait,
    pattern_ir::ConstructorKind,
    trait_def::TraitInstId,
    trait_resolution::{GoalSatisfiability, PredicateListId, TraitSolveCx, is_goal_satisfiable},
    ty_def::CapabilityKind,
};
use hir::hir_def::{EnumVariant, IdentId};
use hir::projection::{Projection, ProjectionPath};

use crate::core_lib::CoreLib;
use crate::ir::{
    AddressSpaceKind, LocalData, LocalId, LocalPlaceRootLayout, MirProjection, ObjectRootSource,
    Place, PointerInfo, RuntimeShape, RuntimeWordKind, ValueData, ValueId,
    lookup_local_pointer_leaf_info, resolve_local_projection_root, try_value_pointer_info_in,
};
use crate::layout;
use common::indexmap::IndexMap;
use rustc_hash::FxHashSet;

/// Canonical representation categories for a type after transparent-newtype peeling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReprKind {
    /// No runtime representation (zero-sized).
    Zst,
    /// A direct EVM word value.
    Word,
    /// An opaque pointer-like EVM word value in an address space.
    Ptr(AddressSpaceKind),
    /// A by-reference aggregate value (pointer into an address space).
    Ref,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PlaceAccessKind {
    Value,
    Location,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PlaceState<'db> {
    pub ty: TyId<'db>,
    pub access_kind: PlaceAccessKind,
    pub address_space: Option<AddressSpaceKind>,
    pub pointer_info: Option<PointerInfo<'db>>,
}

impl<'db> PlaceState<'db> {
    pub fn location_address_space(self) -> Option<AddressSpaceKind> {
        matches!(self.access_kind, PlaceAccessKind::Location)
            .then_some(self.address_space)
            .flatten()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DerefStepKind {
    ReuseLocation,
    UseBaseValue,
    LoadLocationValue,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPlaceProjection<'db> {
    pub projection: MirProjection<'db>,
    pub owner: PlaceState<'db>,
    pub result: PlaceState<'db>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPlaceSegment<'db> {
    pub start_kind: Option<DerefStepKind>,
    pub before: PlaceState<'db>,
    pub base: PlaceState<'db>,
    pub projections: Vec<ResolvedPlaceProjection<'db>>,
}

impl<'db> ResolvedPlaceSegment<'db> {
    pub fn terminal_state(&self) -> PlaceState<'db> {
        self.projections
            .last()
            .map(|projection| projection.result)
            .unwrap_or(self.base)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPlace<'db> {
    pub base: PlaceState<'db>,
    pub segments: Vec<ResolvedPlaceSegment<'db>>,
}

impl<'db> ResolvedPlace<'db> {
    pub fn final_state(&self) -> PlaceState<'db> {
        self.segments
            .last()
            .map(ResolvedPlaceSegment::terminal_state)
            .unwrap_or(self.base)
    }
}

/// Returns the single field type if `ty` is a transparent single-field wrapper.
///
/// Transparent wrappers include:
/// - single-field `struct` ADTs
/// - single-element tuples `(T,)`
///
/// This intentionally does *not* look through nested wrappers. Callers that want to peel multiple
/// levels should loop over this helper.
pub fn transparent_newtype_field_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    if ty.is_tuple(db) {
        let field_tys = ty.field_types(db);
        return (field_tys.len() == 1).then(|| field_tys[0]);
    }

    let base_ty = ty.base_ty(db);
    let TyData::TyBase(TyBase::Adt(adt_def)) = base_ty.data(db) else {
        return None;
    };
    if !matches!(adt_def.adt_ref(db), AdtRef::Struct(_)) {
        return None;
    }
    let field_tys = ty.field_types(db);
    (field_tys.len() == 1).then(|| field_tys[0])
}

/// Returns the field type for a transparent field-0 projection step.
pub fn transparent_field0_inner_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    owner_ty: TyId<'db>,
    field_idx: usize,
) -> Option<TyId<'db>> {
    (field_idx == 0)
        .then(|| transparent_newtype_field_ty(db, owner_ty))
        .flatten()
}

/// Returns the next type for a transparent field-0 projection step.
pub fn transparent_field0_projection_step_ty<'db, Idx>(
    db: &'db dyn HirAnalysisDb,
    owner_ty: TyId<'db>,
    proj: &Projection<TyId<'db>, EnumVariant<'db>, Idx>,
) -> Option<TyId<'db>> {
    let Projection::Field(field_idx) = proj else {
        return None;
    };
    transparent_field0_inner_ty(db, owner_ty, *field_idx)
}

/// Peels a projection path that must consist entirely of transparent field-0 steps.
pub fn peel_transparent_field0_projection_path<'db, Idx>(
    db: &'db dyn HirAnalysisDb,
    mut base_ty: TyId<'db>,
    path: &ProjectionPath<TyId<'db>, EnumVariant<'db>, Idx>,
) -> Option<TyId<'db>> {
    for proj in path.iter() {
        base_ty = transparent_field0_projection_step_ty(db, base_ty, proj)?;
    }
    Some(base_ty)
}

/// Peel all transparent newtype layers from `ty`, returning the first non-newtype type.
pub fn peel_transparent_newtypes<'db>(db: &'db dyn HirAnalysisDb, mut ty: TyId<'db>) -> TyId<'db> {
    while let Some(inner) = transparent_newtype_field_ty(db, ty) {
        ty = inner;
    }
    ty
}

pub fn object_layout_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    mut ty: TyId<'db>,
) -> TyId<'db> {
    let assumptions = PredicateListId::empty_list(db);
    loop {
        ty = normalize_ty(db, ty, core.scope, assumptions);
        if let Some((CapabilityKind::View, inner)) = ty.as_capability(db) {
            ty = inner;
            continue;
        }

        if let Some(inner) = transparent_newtype_field_ty(db, ty) {
            ty = inner;
            continue;
        }

        if let Some((capability, inner)) = ty.as_capability(db)
            && matches!(capability, CapabilityKind::Mut | CapabilityKind::Ref)
            && matches!(repr_kind_for_ty(db, core, inner), ReprKind::Ref)
        {
            ty = inner;
            continue;
        }

        return ty;
    }
}

pub fn supports_object_ref_runtime_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> bool {
    let ty = object_layout_ty(db, core, ty);

    if ty.is_array(db) {
        return layout::array_elem_ty(db, ty)
            .is_none_or(|elem_ty| supports_object_ref_runtime_ty(db, core, elem_ty));
    }

    if ty.is_tuple(db) {
        return ty
            .field_types(db)
            .iter()
            .copied()
            .all(|field_ty| supports_object_ref_runtime_ty(db, core, field_ty));
    }

    if let Some(enum_) = ty.as_enum(db) {
        return (0..enum_.len_variants(db)).all(|idx| {
            let ctor = ConstructorKind::Variant(EnumVariant::new(enum_, idx), ty);
            ctor.field_types(db)
                .iter()
                .copied()
                .all(|field_ty| supports_object_ref_runtime_ty(db, core, field_ty))
        });
    }

    match ty.base_ty(db).data(db) {
        TyData::TyBase(TyBase::Adt(adt_def)) => match adt_def.adt_ref(db) {
            AdtRef::Enum(_) => true,
            AdtRef::Struct(_) => ty
                .field_types(db)
                .iter()
                .copied()
                .all(|field_ty| supports_object_ref_runtime_ty(db, core, field_ty)),
        },
        _ => true,
    }
}

pub fn memory_scalar_object_ref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    let assumptions = PredicateListId::empty_list(db);
    let ty = normalize_ty(db, ty, core.scope, assumptions);

    if effect_provider_space_for_ty(db, core, ty).is_some() {
        return None;
    }

    if let Some((CapabilityKind::View, inner)) = ty.as_capability(db) {
        return memory_scalar_object_ref_target_ty(db, core, inner);
    }
    if ty.as_capability(db).is_some() {
        return None;
    }

    let ty = object_layout_ty(db, core, ty);
    (supports_object_ref_runtime_ty(db, core, ty)
        && matches!(repr_kind_for_ty(db, core, ty), ReprKind::Word))
    .then_some(ty)
}

pub fn memory_scalar_handle_object_ref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    let assumptions = PredicateListId::empty_list(db);
    let ty = normalize_ty(db, ty, core.scope, assumptions);

    if let Some((CapabilityKind::View, inner)) = ty.as_capability(db) {
        return memory_scalar_handle_object_ref_target_ty(db, core, inner);
    }

    let (capability, inner) = ty.as_capability(db)?;
    matches!(capability, CapabilityKind::Mut | CapabilityKind::Ref)
        .then(|| memory_scalar_object_ref_target_ty(db, core, inner))
        .flatten()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MemoryObjectRefClass<'db> {
    Direct { target_ty: TyId<'db> },
    MaterializedScalar { target_ty: TyId<'db> },
    LoadedScalarHandle { target_ty: TyId<'db> },
}

fn classify_memory_object_ref<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<MemoryObjectRefClass<'db>> {
    runtime_object_ref_target_ty(db, core, ty, AddressSpaceKind::Memory)
        .map(|target_ty| MemoryObjectRefClass::Direct { target_ty })
        .or_else(|| {
            memory_scalar_object_ref_target_ty(db, core, ty)
                .map(|target_ty| MemoryObjectRefClass::MaterializedScalar { target_ty })
        })
        .or_else(|| {
            memory_scalar_handle_object_ref_target_ty(db, core, ty)
                .map(|target_ty| MemoryObjectRefClass::LoadedScalarHandle { target_ty })
        })
}

pub fn declared_local_place_root_layout<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    address_space: AddressSpaceKind,
) -> LocalPlaceRootLayout<'db> {
    if address_space != AddressSpaceKind::Memory {
        return LocalPlaceRootLayout::Direct;
    }

    match classify_memory_object_ref(db, core, ty) {
        Some(MemoryObjectRefClass::Direct { target_ty }) => LocalPlaceRootLayout::ObjectRootValue {
            target_ty,
            source: ObjectRootSource::DeclaredByRefAggregate,
        },
        Some(
            MemoryObjectRefClass::MaterializedScalar { .. }
            | MemoryObjectRefClass::LoadedScalarHandle { .. },
        )
        | None => LocalPlaceRootLayout::Direct,
    }
}

fn refresh_declared_local_place_root_layout<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    local: &mut LocalData<'db>,
) {
    local.place_root_layout =
        declared_local_place_root_layout(db, core, local.ty, local.address_space);
}

pub fn set_declared_local_address_space<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    local: &mut LocalData<'db>,
    address_space: AddressSpaceKind,
) {
    local.address_space = address_space;
    refresh_declared_local_place_root_layout(db, core, local);
}

pub fn allocated_local_place_root_layout<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    address_space: AddressSpaceKind,
) -> LocalPlaceRootLayout<'db> {
    if address_space != AddressSpaceKind::Memory {
        return LocalPlaceRootLayout::Direct;
    }

    match classify_memory_object_ref(db, core, ty) {
        Some(
            MemoryObjectRefClass::Direct { target_ty }
            | MemoryObjectRefClass::MaterializedScalar { target_ty },
        ) => LocalPlaceRootLayout::ObjectRootValue {
            target_ty,
            source: ObjectRootSource::AllocatedMemory,
        },
        Some(MemoryObjectRefClass::LoadedScalarHandle { .. }) | None => {
            LocalPlaceRootLayout::MemorySlot
        }
    }
}

pub fn live_place_root_layout<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    address_space: AddressSpaceKind,
) -> LocalPlaceRootLayout<'db> {
    if address_space != AddressSpaceKind::Memory {
        return LocalPlaceRootLayout::Direct;
    }

    match classify_memory_object_ref(db, core, ty) {
        Some(MemoryObjectRefClass::MaterializedScalar { target_ty }) => {
            LocalPlaceRootLayout::ObjectRootStorage {
                target_ty,
                source: ObjectRootSource::MaterializedScalarBorrow,
            }
        }
        Some(
            MemoryObjectRefClass::Direct { .. } | MemoryObjectRefClass::LoadedScalarHandle { .. },
        )
        | None => LocalPlaceRootLayout::MemorySlot,
    }
}

pub fn spill_local_place_root_layout<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    address_space: AddressSpaceKind,
    owner: LocalId,
) -> LocalPlaceRootLayout<'db> {
    if address_space != AddressSpaceKind::Memory {
        return LocalPlaceRootLayout::Direct;
    }

    match classify_memory_object_ref(db, core, ty) {
        Some(
            MemoryObjectRefClass::Direct { target_ty }
            | MemoryObjectRefClass::MaterializedScalar { target_ty },
        ) => LocalPlaceRootLayout::ObjectRootValue {
            target_ty,
            source: ObjectRootSource::SpillOf(owner),
        },
        Some(MemoryObjectRefClass::LoadedScalarHandle { .. }) | None => {
            LocalPlaceRootLayout::MemorySlot
        }
    }
}

pub fn place_root_runtime_shape_for_local<'db>(
    local: &LocalData<'db>,
) -> Option<RuntimeShape<'db>> {
    if local.address_space != AddressSpaceKind::Memory {
        return None;
    }

    match local.place_root_layout {
        LocalPlaceRootLayout::Direct => None,
        LocalPlaceRootLayout::MemorySlot => Some(RuntimeShape::MemoryPtr {
            target_ty: Some(local.ty),
        }),
        LocalPlaceRootLayout::ObjectRootValue { target_ty, .. }
        | LocalPlaceRootLayout::ObjectRootStorage { target_ty, .. } => {
            Some(RuntimeShape::ObjectRef { target_ty })
        }
    }
}

pub fn enum_is_payload_free<'db>(db: &'db dyn HirAnalysisDb, ty: TyId<'db>) -> bool {
    let Some(enum_) = ty.as_enum(db) else {
        return false;
    };
    (0..enum_.len_variants(db)).all(|idx| {
        let ctor = ConstructorKind::Variant(EnumVariant::new(enum_, idx), ty);
        ctor.field_types(db).is_empty()
    })
}

/// Returns the effect provider's address space for a type, looking through transparent newtype wrappers.
pub fn effect_provider_space_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<AddressSpaceKind> {
    if let Some((_, inner)) = ty.as_capability(db) {
        return effect_provider_space_for_ty(db, core, inner);
    }

    if let Some(space) = effect_provider_space_via_domain_trait(db, core, ty) {
        return Some(space);
    }

    transparent_newtype_field_ty(db, ty)
        .and_then(|inner| effect_provider_space_for_ty(db, core, inner))
}

/// Returns the normalized `EffectHandle::Target` type for an effect provider, looking through
/// transparent newtype wrappers.
pub fn effect_provider_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    if let Some(target) = direct_deref_target_ty(db, core, ty) {
        return Some(target);
    }

    transparent_newtype_field_ty(db, ty)
        .and_then(|inner| effect_provider_target_ty(db, core, inner))
}

pub fn direct_deref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    if let Some((_, inner)) = ty.as_capability(db) {
        return Some(inner);
    }

    let effect_handle = resolve_core_trait(db, core.scope, &["effect_ref", "EffectHandle"])
        .expect("missing required core trait `core::effect_ref::EffectHandle`");
    let assumptions = PredicateListId::empty_list(db);
    let target_ident = IdentId::new(db, "Target".to_string());
    let inst = TraitInstId::new(db, effect_handle, vec![ty], IndexMap::new());
    match is_goal_satisfiable(
        db,
        TraitSolveCx::new(db, core.scope).with_assumptions(assumptions),
        inst,
    ) {
        GoalSatisfiability::Satisfied(_) => inst
            .assoc_ty(db, target_ident)
            .map(|assoc| normalize_ty(db, assoc, core.scope, assumptions))
            .filter(|target| !target.has_invalid(db)),
        GoalSatisfiability::NeedsConfirmation(_)
        | GoalSatisfiability::ContainsInvalid
        | GoalSatisfiability::UnSat(_) => None,
    }
}

pub fn deref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<TyId<'db>> {
    direct_deref_target_ty(db, core, ty).or_else(|| {
        transparent_newtype_field_ty(db, ty).and_then(|inner| deref_target_ty(db, core, inner))
    })
}

pub fn pointer_info_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_ref_space: AddressSpaceKind,
) -> Option<PointerInfo<'db>> {
    if let Some((capability, inner)) = ty.as_capability(db) {
        return match capability {
            CapabilityKind::Mut => Some(PointerInfo {
                address_space: default_ref_space,
                target_ty: Some(inner),
            }),
            CapabilityKind::Ref => Some(PointerInfo {
                address_space: default_ref_space,
                target_ty: Some(inner),
            }),
            CapabilityKind::View => pointer_info_for_ty(db, core, inner, default_ref_space),
        };
    }

    if let Some(space) = effect_provider_space_for_ty(db, core, ty) {
        return Some(PointerInfo {
            address_space: space,
            target_ty: effect_provider_target_ty(db, core, ty),
        });
    }

    transparent_newtype_field_ty(db, ty)
        .and_then(|inner| pointer_info_for_ty(db, core, inner, default_ref_space))
}

pub fn handle_pointer_info_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_ref_space: AddressSpaceKind,
) -> Option<PointerInfo<'db>> {
    if let Some((capability, inner)) = ty.as_capability(db) {
        let target_ty = deref_target_ty(db, core, inner).unwrap_or(inner);
        let target_ty = if default_ref_space == AddressSpaceKind::Memory
            && supports_object_ref_runtime_ty(db, core, target_ty)
        {
            object_layout_ty(db, core, target_ty)
        } else {
            target_ty
        };
        return match capability {
            CapabilityKind::Mut | CapabilityKind::Ref => Some(PointerInfo {
                address_space: default_ref_space,
                target_ty: Some(target_ty),
            }),
            CapabilityKind::View => handle_pointer_info_for_ty(db, core, inner, default_ref_space),
        };
    }

    if let Some(address_space) = effect_provider_space_for_ty(db, core, ty) {
        return Some(PointerInfo {
            address_space,
            target_ty: effect_provider_target_ty(db, core, ty),
        });
    }

    transparent_newtype_field_ty(db, ty)
        .and_then(|inner| handle_pointer_info_for_ty(db, core, inner, default_ref_space))
}

pub fn runtime_pointer_info_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_ref_space: AddressSpaceKind,
) -> Option<PointerInfo<'db>> {
    if let Some(info) = pointer_info_for_ty(db, core, ty, default_ref_space) {
        return Some(info);
    }

    matches!(repr_kind_for_ty(db, core, ty), ReprKind::Ref).then_some(PointerInfo {
        address_space: default_ref_space,
        target_ty: Some(ty),
    })
}

pub fn runtime_value_pointer_info_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    address_space: AddressSpaceKind,
) -> Option<PointerInfo<'db>> {
    runtime_pointer_info_for_ty(db, core, ty, address_space)
        .or_else(|| handle_pointer_info_for_ty(db, core, ty, address_space))
}

pub(crate) fn infer_value_pointer_info<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    value: ValueId,
) -> Option<PointerInfo<'db>> {
    let value_data = values.get(value.index())?;
    let typed_info_for_space =
        |address_space| runtime_value_pointer_info_for_ty(db, core, value_data.ty, address_space);
    let place_value_pointer_info = |place: &crate::ir::Place<'db>| {
        crate::ir::try_place_pointer_info_in(values, locals, place)
            .or_else(|| {
                crate::ir::try_place_address_space_in(values, locals, place).map(|address_space| {
                    PointerInfo {
                        address_space,
                        target_ty: None,
                    }
                })
            })
            .and_then(|info| typed_info_for_space(info.address_space))
    };

    match &value_data.origin {
        crate::ir::ValueOrigin::Local(local) | crate::ir::ValueOrigin::PlaceRoot(local) => {
            locals.get(local.index()).and_then(|local_data| {
                crate::ir::lookup_local_pointer_leaf_info(
                    locals,
                    *local,
                    &crate::MirProjectionPath::new(),
                )
                .or_else(|| typed_info_for_space(local_data.address_space))
                .or(value_data.pointer_info)
            })
        }
        crate::ir::ValueOrigin::TransparentCast { value: inner } => {
            value_data.pointer_info.or_else(|| {
                crate::ir::try_value_address_space_in(values, locals, *inner)
                    .and_then(typed_info_for_space)
                    .or_else(|| {
                        infer_value_pointer_info(db, core, values, locals, *inner)
                            .and_then(|info| typed_info_for_space(info.address_space))
                    })
                    .or_else(|| {
                        value_data
                            .repr
                            .address_space()
                            .and_then(typed_info_for_space)
                    })
            })
        }
        crate::ir::ValueOrigin::FieldPtr(field_ptr) => value_data
            .pointer_info
            .or_else(|| {
                runtime_value_pointer_info_for_ty(db, core, value_data.ty, field_ptr.addr_space)
            })
            .or(Some(PointerInfo {
                address_space: field_ptr.addr_space,
                target_ty: None,
            })),
        crate::ir::ValueOrigin::PlaceRef(place) | crate::ir::ValueOrigin::MoveOut { place } => {
            place_value_pointer_info(place)
                .or_else(|| {
                    value_data
                        .repr
                        .address_space()
                        .and_then(typed_info_for_space)
                })
                .or(value_data.pointer_info)
        }
        _ => value_data.pointer_info.or_else(|| {
            value_data
                .repr
                .address_space()
                .and_then(typed_info_for_space)
        }),
    }
}

fn place_base_access_kind<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    value: &ValueData<'db>,
    pointer_info: Option<PointerInfo<'db>>,
    place: &Place<'db>,
) -> PlaceAccessKind {
    if (value.repr.is_ref() && matches!(repr_kind_for_ty(db, core, value.ty), ReprKind::Ref))
        || pointer_info.is_some_and(|info| info.target_ty == Some(value.ty))
        || (place.projection.is_empty()
            && pointer_info.is_some_and(|info| info.target_ty.is_none()))
        || matches!(
            value.origin,
            crate::ir::ValueOrigin::PlaceRoot(_)
                | crate::ir::ValueOrigin::PlaceRef(_)
                | crate::ir::ValueOrigin::FieldPtr(_)
        )
    {
        return PlaceAccessKind::Location;
    }

    PlaceAccessKind::Value
}

fn projection_result_ty<'db, Idx>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    current: PlaceState<'db>,
    proj: &Projection<TyId<'db>, EnumVariant<'db>, Idx>,
) -> Option<TyId<'db>> {
    match proj {
        Projection::Field(field_idx) => current.ty.field_types(db).get(*field_idx).copied(),
        Projection::VariantField {
            variant,
            enum_ty,
            field_idx,
        } => {
            let ctor = ConstructorKind::Variant(*variant, *enum_ty);
            ctor.field_types(db).get(*field_idx).copied()
        }
        Projection::Discriminant => Some(TyId::new(
            db,
            TyData::TyBase(TyBase::Prim(hir::analysis::ty::ty_def::PrimTy::U256)),
        )),
        Projection::Index(_) => {
            let (base, args) = current.ty.decompose_ty_app(db);
            (base.is_array(db) && !args.is_empty()).then_some(args[0])
        }
        Projection::Deref => current
            .ty
            .as_capability(db)
            .map(|(_, inner)| inner)
            .or_else(|| effect_provider_target_ty(db, core, current.ty))
            .or_else(|| current.pointer_info.and_then(|info| info.target_ty)),
    }
}

fn state_pointer_info<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    locals: &[LocalData<'db>],
    local_root: Option<&(
        crate::LocalId,
        ProjectionPath<TyId<'db>, EnumVariant<'db>, ValueId>,
    )>,
    ty: TyId<'db>,
    address_space: Option<AddressSpaceKind>,
) -> Option<PointerInfo<'db>> {
    if let Some((local, path)) = local_root
        && let Some(info) = crate::ir::lookup_local_pointer_leaf_info(locals, *local, path)
    {
        return Some(info);
    }

    address_space.and_then(|space| runtime_pointer_info_for_ty(db, core, ty, space))
}

fn resolve_deref_step<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    locals: &[LocalData<'db>],
    local_root: &mut Option<(
        crate::LocalId,
        ProjectionPath<TyId<'db>, EnumVariant<'db>, ValueId>,
    )>,
    owner: PlaceState<'db>,
) -> Option<(DerefStepKind, PlaceState<'db>)> {
    let deref = Projection::<TyId<'db>, EnumVariant<'db>, ValueId>::Deref;
    let ty = projection_result_ty(db, core, owner, &deref)?;
    if matches!(owner.access_kind, PlaceAccessKind::Location)
        && matches!(repr_kind_for_ty(db, core, owner.ty), ReprKind::Ref)
    {
        return Some((
            DerefStepKind::ReuseLocation,
            PlaceState {
                ty,
                access_kind: PlaceAccessKind::Location,
                address_space: owner.address_space,
                pointer_info: state_pointer_info(
                    db,
                    core,
                    locals,
                    local_root.as_ref(),
                    ty,
                    owner.address_space,
                ),
            },
        ));
    }

    let info = owner.pointer_info?;
    *local_root = None;
    let address_space = Some(info.address_space);
    let start_kind = if matches!(owner.access_kind, PlaceAccessKind::Value) {
        DerefStepKind::UseBaseValue
    } else {
        DerefStepKind::LoadLocationValue
    };
    Some((
        start_kind,
        PlaceState {
            ty,
            access_kind: PlaceAccessKind::Location,
            address_space,
            pointer_info: runtime_pointer_info_for_ty(db, core, ty, info.address_space),
        },
    ))
}

pub fn resolve_place<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
) -> Option<ResolvedPlace<'db>> {
    let base_value = values.get(place.base.index())?;
    let mut local_root = crate::ir::resolve_local_projection_root(values, place.base);
    let root_address_space = crate::ir::try_value_address_space_in(values, locals, place.base);
    let base_pointer_info = state_pointer_info(
        db,
        core,
        locals,
        local_root.as_ref(),
        base_value.ty,
        root_address_space,
    )
    .or_else(|| crate::ir::try_value_pointer_info_in(values, locals, place.base));
    let base_access_kind = place_base_access_kind(db, core, base_value, base_pointer_info, place);
    let base_address_space = matches!(base_access_kind, PlaceAccessKind::Location)
        .then_some(root_address_space)
        .flatten();
    let base_state = PlaceState {
        ty: base_value.ty,
        access_kind: base_access_kind,
        address_space: base_address_space,
        pointer_info: base_pointer_info,
    };

    let mut current = base_state;
    let mut segments = Vec::new();
    let mut segment = ResolvedPlaceSegment {
        start_kind: None,
        before: base_state,
        base: base_state,
        projections: Vec::new(),
    };
    for proj in place.projection.iter().cloned() {
        let owner = current;
        current = match proj {
            Projection::Deref => {
                let (start_kind, next_state) =
                    resolve_deref_step(db, core, locals, &mut local_root, owner)?;

                if !segment.projections.is_empty() {
                    segments.push(segment);
                }
                segment = ResolvedPlaceSegment {
                    start_kind: Some(start_kind),
                    before: owner,
                    base: next_state,
                    projections: Vec::new(),
                };
                next_state
            }
            _ => {
                if !matches!(owner.access_kind, PlaceAccessKind::Location) {
                    return None;
                }
                let ty = projection_result_ty(db, core, owner, &proj)?;
                if let Some((_, path)) = &mut local_root {
                    path.push(proj.clone());
                }
                let address_space = owner.address_space;
                let next_state = PlaceState {
                    ty,
                    access_kind: PlaceAccessKind::Location,
                    address_space,
                    pointer_info: state_pointer_info(
                        db,
                        core,
                        locals,
                        local_root.as_ref(),
                        ty,
                        address_space,
                    ),
                };
                segment.projections.push(ResolvedPlaceProjection {
                    projection: proj,
                    owner,
                    result: next_state,
                });
                next_state
            }
        };
    }

    if !segment.projections.is_empty()
        || segment.start_kind.is_some()
        || place.projection.is_empty()
    {
        segments.push(segment);
    }

    Some(ResolvedPlace {
        base: base_state,
        segments,
    })
}

pub fn place_yields_location_value<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
    value_ty: TyId<'db>,
    pointer_info: Option<PointerInfo<'db>>,
) -> Option<bool> {
    let assumptions = PredicateListId::empty_list(db);
    let final_state = resolve_place(db, core, values, locals, place)?.final_state();
    if final_state.location_address_space().is_none() {
        return Some(false);
    }
    let final_ty = normalize_ty(db, final_state.ty, core.scope, assumptions);
    let value_ty = normalize_ty(db, value_ty, core.scope, assumptions);
    let value_repr = repr_kind_for_ty(db, core, value_ty);

    if matches!(value_repr, ReprKind::Ref)
        && final_state.location_address_space() == Some(AddressSpaceKind::Memory)
        && runtime_ty_matches(db, final_ty, value_ty)
    {
        return Some(true);
    }

    if matches!(value_repr, ReprKind::Ptr(_)) && runtime_ty_matches(db, final_ty, value_ty) {
        return Some(false);
    }

    if direct_deref_target_ty(db, core, value_ty)
        .map(|target| normalize_ty(db, target, core.scope, assumptions))
        .is_some_and(|target| runtime_ty_matches(db, target, final_ty))
    {
        return Some(true);
    }

    if pointer_info
        .and_then(|info| info.target_ty)
        .is_some_and(|target| {
            runtime_ty_matches(
                db,
                normalize_ty(db, target, core.scope, assumptions),
                final_ty,
            )
        })
    {
        return Some(true);
    }

    Some(false)
}

pub(crate) fn runtime_ty_matches<'db>(
    db: &'db dyn HirAnalysisDb,
    lhs: TyId<'db>,
    rhs: TyId<'db>,
) -> bool {
    let lhs = peel_transparent_newtypes(db, lhs);
    let rhs = peel_transparent_newtypes(db, rhs);
    lhs == rhs || lhs.pretty_print(db) == rhs.pretty_print(db)
}

fn effect_provider_space_via_domain_trait<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Option<AddressSpaceKind> {
    let effect_handle = resolve_core_trait(db, core.scope, &["effect_ref", "EffectHandle"])
        .expect("missing required core trait `core::effect_ref::EffectHandle`");
    let assumptions = PredicateListId::empty_list(db);

    let address_space_ident = IdentId::new(db, "AddressSpace".to_string());

    // First, determine whether `ty` is an effect provider at all.
    let inst = TraitInstId::new(db, effect_handle, vec![ty], IndexMap::new());
    match is_goal_satisfiable(
        db,
        TraitSolveCx::new(db, core.scope).with_assumptions(assumptions),
        inst,
    ) {
        GoalSatisfiability::Satisfied(_) => {}
        GoalSatisfiability::NeedsConfirmation(_) => return None,
        GoalSatisfiability::ContainsInvalid | GoalSatisfiability::UnSat(_) => return None,
    }

    for (space_ty, space_kind) in [
        (core.addr_space_mem, AddressSpaceKind::Memory),
        (core.addr_space_calldata, AddressSpaceKind::Calldata),
        (
            core.addr_space_transient,
            AddressSpaceKind::TransientStorage,
        ),
        (core.addr_space_stor, AddressSpaceKind::Storage),
    ] {
        let mut assoc = IndexMap::new();
        assoc.insert(address_space_ident, space_ty);
        let inst = TraitInstId::new(db, effect_handle, vec![ty], assoc);
        match is_goal_satisfiable(
            db,
            TraitSolveCx::new(db, core.scope).with_assumptions(assumptions),
            inst,
        ) {
            GoalSatisfiability::Satisfied(_) => return Some(space_kind),
            GoalSatisfiability::NeedsConfirmation(_) => return None,
            GoalSatisfiability::ContainsInvalid | GoalSatisfiability::UnSat(_) => {}
        }
    }

    panic!(
        "`{}` implements `EffectHandle` but `AddressSpace` is not one of: core::effect_ref::Memory | Calldata | Storage | TransientStorage",
        ty.pretty_print(db)
    )
}

/// Computes the canonical MIR representation kind for `ty`.
///
/// This is the single source of truth used by MIR lowering and post-processing. In particular,
/// transparent newtypes are recursively unwrapped so `struct A { b: Foo }` inherits the runtime
/// representation of `Foo`, and so on.
pub fn repr_kind_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> ReprKind {
    if layout::is_zero_sized_ty(db, ty) {
        return ReprKind::Zst;
    }

    if let Some((capability, inner)) = ty.as_capability(db) {
        return match capability {
            CapabilityKind::Mut => ReprKind::Ptr(AddressSpaceKind::Memory),
            CapabilityKind::Ref => repr_kind_for_ref_inner(db, core, inner),
            CapabilityKind::View => repr_kind_for_ty(db, core, inner),
        };
    }

    if let Some(space) = effect_provider_space_for_ty(db, core, ty) {
        return ReprKind::Ptr(space);
    }

    if let Some(inner) = transparent_newtype_field_ty(db, ty) {
        return repr_kind_for_ty(db, core, inner);
    }

    if ty.is_array(db) || ty.is_tuple(db) {
        return ReprKind::Ref;
    }

    if ty
        .adt_ref(db)
        .is_some_and(|adt| matches!(adt, AdtRef::Struct(_)))
    {
        return ReprKind::Ref;
    }

    if ty.as_enum(db).is_some() {
        return if enum_is_payload_free(db, ty) {
            ReprKind::Word
        } else {
            ReprKind::Ref
        };
    }

    ReprKind::Word
}

fn repr_kind_for_ref_inner<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    inner: TyId<'db>,
) -> ReprKind {
    match repr_kind_for_ty(db, core, inner) {
        ReprKind::Word | ReprKind::Zst | ReprKind::Ptr(_) => {
            ReprKind::Ptr(AddressSpaceKind::Memory)
        }
        ReprKind::Ref => ReprKind::Ptr(AddressSpaceKind::Memory),
    }
}

/// Returns the leaf type that should drive word conversion (`WordRepr::{from_word,to_word}`).
///
/// This peels transparent newtypes and view wrappers so `struct WrapU8 { inner: u8 }` and
/// `view u8` are treated like `u8` for the purposes of masking/sign-extension.
pub fn word_conversion_leaf_ty<'db>(db: &'db dyn HirAnalysisDb, ty: TyId<'db>) -> TyId<'db> {
    let mut ty = ty;
    loop {
        if let Some((CapabilityKind::View, inner)) = ty.as_capability(db) {
            ty = inner;
            continue;
        }
        if let Some(inner) = transparent_newtype_field_ty(db, ty) {
            ty = inner;
            continue;
        }
        return ty;
    }
}

pub fn runtime_word_kind_for_ty<'db>(db: &'db dyn HirAnalysisDb, ty: TyId<'db>) -> RuntimeWordKind {
    let leaf_ty = word_conversion_leaf_ty(db, ty);
    if let TyData::TyBase(TyBase::Prim(prim)) = leaf_ty.base_ty(db).data(db) {
        return match prim {
            hir::analysis::ty::ty_def::PrimTy::Bool => RuntimeWordKind::I1,
            hir::analysis::ty::ty_def::PrimTy::U8 | hir::analysis::ty::ty_def::PrimTy::I8 => {
                RuntimeWordKind::I8
            }
            hir::analysis::ty::ty_def::PrimTy::U16 | hir::analysis::ty::ty_def::PrimTy::I16 => {
                RuntimeWordKind::I16
            }
            hir::analysis::ty::ty_def::PrimTy::U32 | hir::analysis::ty::ty_def::PrimTy::I32 => {
                RuntimeWordKind::I32
            }
            hir::analysis::ty::ty_def::PrimTy::U64 | hir::analysis::ty::ty_def::PrimTy::I64 => {
                RuntimeWordKind::I64
            }
            hir::analysis::ty::ty_def::PrimTy::U128 | hir::analysis::ty::ty_def::PrimTy::I128 => {
                RuntimeWordKind::I128
            }
            hir::analysis::ty::ty_def::PrimTy::U256
            | hir::analysis::ty::ty_def::PrimTy::I256
            | hir::analysis::ty::ty_def::PrimTy::Usize
            | hir::analysis::ty::ty_def::PrimTy::Isize
            | hir::analysis::ty::ty_def::PrimTy::String
            | hir::analysis::ty::ty_def::PrimTy::Array
            | hir::analysis::ty::ty_def::PrimTy::Tuple(_)
            | hir::analysis::ty::ty_def::PrimTy::Ptr
            | hir::analysis::ty::ty_def::PrimTy::View
            | hir::analysis::ty::ty_def::PrimTy::BorrowMut
            | hir::analysis::ty::ty_def::PrimTy::BorrowRef => RuntimeWordKind::I256,
        };
    }

    RuntimeWordKind::I256
}

pub fn runtime_shape_for_pointer_info<'db>(info: PointerInfo<'db>) -> RuntimeShape<'db> {
    if info.address_space != AddressSpaceKind::Memory {
        return RuntimeShape::AddressWord(info);
    }

    RuntimeShape::MemoryPtr {
        target_ty: info.target_ty,
    }
}

fn runtime_object_ref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_ref_space: AddressSpaceKind,
) -> Option<TyId<'db>> {
    let assumptions = PredicateListId::empty_list(db);
    let ty = normalize_ty(db, ty, core.scope, assumptions);
    if default_ref_space != AddressSpaceKind::Memory {
        return None;
    }

    if let Some((capability, inner)) = ty.as_capability(db) {
        return match capability {
            CapabilityKind::View => {
                runtime_object_ref_target_ty(db, core, inner, default_ref_space)
            }
            CapabilityKind::Mut | CapabilityKind::Ref => {
                runtime_object_ref_target_ty(db, core, inner, default_ref_space)
            }
        };
    }

    if effect_provider_space_for_ty(db, core, ty).is_some() {
        return None;
    }

    if let Some(inner) = transparent_newtype_field_ty(db, ty) {
        return runtime_object_ref_target_ty(db, core, inner, default_ref_space);
    }

    if !supports_object_ref_runtime_ty(db, core, ty) {
        return None;
    }

    matches!(repr_kind_for_ty(db, core, ty), ReprKind::Ref).then(|| object_layout_ty(db, core, ty))
}

fn runtime_shape_needs_dynamic_address_space<'db>(
    db: &'db dyn HirAnalysisDb,
    ty: TyId<'db>,
) -> bool {
    if let Some((capability, inner)) = ty.as_capability(db) {
        return match capability {
            CapabilityKind::Mut | CapabilityKind::Ref => true,
            CapabilityKind::View => runtime_shape_needs_dynamic_address_space(db, inner),
        };
    }

    transparent_newtype_field_ty(db, ty)
        .is_some_and(|inner| runtime_shape_needs_dynamic_address_space(db, inner))
}

pub fn runtime_shape_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_ref_space: AddressSpaceKind,
) -> RuntimeShape<'db> {
    if layout::is_zero_sized_ty(db, ty) {
        return RuntimeShape::Erased;
    }

    if default_ref_space == AddressSpaceKind::Memory
        && let Some(MemoryObjectRefClass::Direct { target_ty }) =
            classify_memory_object_ref(db, core, ty)
    {
        return RuntimeShape::ObjectRef { target_ty };
    }

    if let Some(info) = runtime_pointer_info_for_ty(db, core, ty, default_ref_space) {
        return runtime_shape_for_pointer_info(info);
    }

    RuntimeShape::Word(runtime_word_kind_for_ty(db, ty))
}

pub fn runtime_return_shape_seed_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> RuntimeShape<'db> {
    if layout::is_zero_sized_ty(db, ty) {
        return RuntimeShape::Erased;
    }

    if runtime_shape_needs_dynamic_address_space(db, ty) {
        return RuntimeShape::Unresolved;
    }

    runtime_shape_for_ty(db, core, ty, AddressSpaceKind::Memory)
}

pub fn runtime_shape_for_local<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    local: &LocalData<'db>,
) -> RuntimeShape<'db> {
    if let LocalPlaceRootLayout::ObjectRootValue { target_ty, .. } = local.place_root_layout
        && local.address_space == AddressSpaceKind::Memory
    {
        return RuntimeShape::ObjectRef { target_ty };
    }

    let type_shape = runtime_shape_for_ty(db, core, local.ty, local.address_space);
    if let Some((_, info)) = local
        .pointer_leaf_infos
        .iter()
        .find(|(path, _)| path.is_empty())
        && (info.address_space != AddressSpaceKind::Memory
            || matches!(type_shape, RuntimeShape::Word(_)))
    {
        return runtime_shape_for_pointer_info(*info);
    }

    type_shape
}

fn try_normalize_pointer_leaf_infos<'db>(
    infos: Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
) -> Result<
    Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
    crate::capability_space::PointerInfoConflict<'db>,
> {
    crate::capability_space::normalize_pointer_leaf_info_entries(infos)
}

pub fn normalize_pointer_leaf_infos<'db>(
    infos: Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
) -> Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)> {
    try_normalize_pointer_leaf_infos(infos)
        .expect("MIR pointer leaf info conflicts should be resolved before runtime layout queries")
}

pub(crate) fn try_pointer_leaf_infos_for_projection_from_entries<'db>(
    infos: &[(crate::MirProjectionPath<'db>, PointerInfo<'db>)],
    projection: &crate::MirProjectionPath<'db>,
) -> Result<
    Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
    crate::capability_space::PointerInfoConflict<'db>,
> {
    let mut projected = Vec::new();
    for (path, info) in infos {
        if let Some(suffix) = crate::ir::projection_strip_prefix(path, projection) {
            projected.push((suffix, *info));
        }
    }
    try_normalize_pointer_leaf_infos(projected)
}

fn enum_tag_owner_place<'db>(place: &Place<'db>) -> Option<Place<'db>> {
    let Some(Projection::Discriminant) = place.projection.iter().last() else {
        return None;
    };
    let mut owner_projection = crate::MirProjectionPath::new();
    for projection in place
        .projection
        .iter()
        .take(place.projection.len().saturating_sub(1))
    {
        owner_projection.push(projection.clone());
    }
    Some(Place::new(place.base, owner_projection))
}

fn try_pointer_leaf_infos_for_enum_tag_place_with_fallback<'db, F>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
    fallback_place_address_space: &F,
) -> Result<
    Option<Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>>,
    crate::capability_space::PointerInfoConflict<'db>,
>
where
    F: Fn(&Place<'db>) -> AddressSpaceKind,
{
    let Some(owner_place) = enum_tag_owner_place(place) else {
        return Ok(None);
    };
    let Some(enum_ty) = place_object_ref_target_ty(db, core, values, locals, &owner_place) else {
        return Ok(None);
    };
    if enum_ty.as_enum(db).is_none() {
        return Ok(None);
    }
    let owner_infos = try_pointer_leaf_infos_for_place_with_fallback(
        db,
        core,
        values,
        locals,
        &owner_place,
        enum_ty,
        fallback_place_address_space,
    )?;
    Ok(Some(
        owner_infos
            .into_iter()
            .filter(|(path, _)| !path.is_empty())
            .collect(),
    ))
}

pub(crate) fn try_pointer_leaf_infos_for_place_with_fallback<'db, F>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
    target_ty: TyId<'db>,
    fallback_place_address_space: &F,
) -> Result<
    Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
    crate::capability_space::PointerInfoConflict<'db>,
>
where
    F: Fn(&Place<'db>) -> AddressSpaceKind,
{
    if let Some(enum_tag_infos) = try_pointer_leaf_infos_for_enum_tag_place_with_fallback(
        db,
        core,
        values,
        locals,
        place,
        fallback_place_address_space,
    )? {
        return Ok(enum_tag_infos);
    }

    let resolved = resolve_place(db, core, values, locals, place);
    let crosses_deref_boundary = resolved.as_ref().is_some_and(|resolved| {
        resolved
            .segments
            .iter()
            .any(|segment| segment.start_kind.is_some())
    });
    let target_space = resolved
        .as_ref()
        .and_then(|resolved| {
            let final_state = resolved.final_state();
            final_state
                .pointer_info
                .map(|info| info.address_space)
                .or(final_state.location_address_space())
        })
        .unwrap_or_else(|| fallback_place_address_space(place));
    let target_infos = crate::capability_space::pointer_leaf_infos_for_ty_with_default(
        db,
        core,
        target_ty,
        target_space,
    );
    if !crosses_deref_boundary
        && let Some((local, base_projection)) =
            crate::ir::resolve_local_projection_root(values, place.base)
        && let Some(local_data) = locals.get(local.index())
    {
        let full_projection = base_projection.concat(&place.projection);
        let infos = try_pointer_leaf_infos_for_projection_from_entries(
            &local_data.pointer_leaf_infos,
            &full_projection,
        )?;
        if !infos.is_empty() {
            if place_object_ref_target_ty(db, core, values, locals, place).is_some() {
                let local_paths: FxHashSet<_> =
                    infos.iter().map(|(path, _)| path.clone()).collect();
                return Ok(infos
                    .into_iter()
                    .chain(
                        target_infos
                            .into_iter()
                            .filter(|(path, _)| !path.is_empty() && !local_paths.contains(path)),
                    )
                    .collect());
            }

            if target_infos.is_empty() {
                return Ok(Vec::new());
            }

            let target_paths: FxHashSet<_> =
                target_infos.iter().map(|(path, _)| path.clone()).collect();
            let local_infos: Vec<_> = infos
                .into_iter()
                .filter(|(path, _)| target_paths.contains(path))
                .collect();
            if local_infos.is_empty() {
                return Ok(target_infos);
            }

            let local_paths: FxHashSet<_> =
                local_infos.iter().map(|(path, _)| path.clone()).collect();
            return Ok(local_infos
                .into_iter()
                .chain(
                    target_infos
                        .into_iter()
                        .filter(|(path, _)| !local_paths.contains(path)),
                )
                .collect());
        }
    }

    Ok(target_infos)
}

pub fn pointer_leaf_infos_for_place<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
    target_ty: TyId<'db>,
) -> Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)> {
    let fallback = |place: &Place<'db>| {
        crate::ir::try_place_address_space_in(values, locals, place)
            .unwrap_or(AddressSpaceKind::Memory)
    };
    try_pointer_leaf_infos_for_place_with_fallback(
        db, core, values, locals, place, target_ty, &fallback,
    )
    .expect("MIR pointer leaf info conflicts should be resolved before runtime layout queries")
}

pub(crate) fn try_pointer_leaf_infos_for_value_with_fallback<'db, F>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    value: ValueId,
    fallback_place_address_space: &F,
) -> Result<
    Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
    crate::capability_space::PointerInfoConflict<'db>,
>
where
    F: Fn(&Place<'db>) -> AddressSpaceKind,
{
    let Some(value_data) = values.get(value.index()) else {
        return Ok(Vec::new());
    };
    Ok(match &value_data.origin {
        crate::ir::ValueOrigin::Local(local) | crate::ir::ValueOrigin::PlaceRoot(local) => locals
            .get(local.index())
            .map(|local| local.pointer_leaf_infos.clone())
            .unwrap_or_default(),
        crate::ir::ValueOrigin::TransparentCast { value: inner } => {
            let infos = try_pointer_leaf_infos_for_value_with_fallback(
                db,
                core,
                values,
                locals,
                *inner,
                fallback_place_address_space,
            )?;
            if !infos.is_empty() {
                return Ok(infos);
            }
            crate::ir::try_value_address_space_in(values, locals, *inner)
                .and_then(|space| runtime_value_pointer_info_for_ty(db, core, value_data.ty, space))
                .map(|info| vec![(crate::MirProjectionPath::new(), info)])
                .unwrap_or_default()
        }
        crate::ir::ValueOrigin::PlaceRef(place) | crate::ir::ValueOrigin::MoveOut { place } => {
            return try_pointer_leaf_infos_for_place_with_fallback(
                db,
                core,
                values,
                locals,
                place,
                value_data.ty,
                fallback_place_address_space,
            );
        }
        crate::ir::ValueOrigin::FieldPtr(field_ptr) => {
            pointer_info_for_ty(db, core, value_data.ty, field_ptr.addr_space)
                .map(|info| vec![(crate::MirProjectionPath::new(), info)])
                .unwrap_or_default()
        }
        _ => try_value_pointer_info_in(values, locals, value)
            .filter(|_| {
                pointer_info_for_ty(db, core, value_data.ty, AddressSpaceKind::Memory).is_some()
            })
            .map(|info| vec![(crate::MirProjectionPath::new(), info)])
            .unwrap_or_default(),
    })
}

pub fn pointer_leaf_infos_for_value<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    value: ValueId,
) -> Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)> {
    let fallback = |place: &Place<'db>| {
        crate::ir::try_place_address_space_in(values, locals, place)
            .unwrap_or(AddressSpaceKind::Memory)
    };
    try_pointer_leaf_infos_for_value_with_fallback(db, core, values, locals, value, &fallback)
        .expect("MIR pointer leaf info conflicts should be resolved before runtime layout queries")
}

fn value_object_ref_target_ty<'db>(
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    mut value: ValueId,
) -> Option<TyId<'db>> {
    loop {
        match &values.get(value.index())?.origin {
            crate::ir::ValueOrigin::Local(local) => {
                let local = locals.get(local.index())?;
                if local.address_space != AddressSpaceKind::Memory {
                    return None;
                }
                return match local.runtime_shape {
                    RuntimeShape::ObjectRef { target_ty } => Some(target_ty),
                    _ => None,
                };
            }
            crate::ir::ValueOrigin::PlaceRoot(local) => {
                let local = locals.get(local.index())?;
                return (local.address_space == AddressSpaceKind::Memory)
                    .then(|| local.place_root_layout.object_target_ty())
                    .flatten();
            }
            crate::ir::ValueOrigin::TransparentCast { value: inner } => value = *inner,
            crate::ir::ValueOrigin::PlaceRef(place) | crate::ir::ValueOrigin::MoveOut { place } => {
                value = place.base;
            }
            crate::ir::ValueOrigin::FieldPtr(field_ptr) => value = field_ptr.base,
            _ => return None,
        }
    }
}

fn resolved_place_has_object_root_layout<'db>(
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
    resolved: &ResolvedPlace<'db>,
) -> bool {
    if value_object_ref_target_ty(values, locals, place.base).is_none() {
        return false;
    }

    for segment in &resolved.segments {
        if segment.base.location_address_space() != Some(AddressSpaceKind::Memory) {
            return false;
        }
        for projection in &segment.projections {
            if matches!(
                projection.projection,
                Projection::Discriminant | Projection::Deref
            ) {
                return false;
            }
        }
    }

    true
}

fn exact_local_place_leaf_pointer_info<'db>(
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
) -> Option<PointerInfo<'db>> {
    let (local, mut path) = resolve_local_projection_root(values, place.base)?;
    let local_data = locals.get(local.index())?;
    for projection in place.projection.iter() {
        if matches!(projection, Projection::Deref) {
            if !local_data
                .pointer_leaf_infos
                .iter()
                .any(|(leaf_path, _)| path.is_prefix_of(leaf_path))
            {
                return None;
            }
            continue;
        }
        path.push(projection.clone());
    }
    lookup_local_pointer_leaf_info(locals, local, &path)
}

pub fn place_object_ref_target_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
) -> Option<TyId<'db>> {
    let resolved = resolve_place(db, core, values, locals, place)?;
    if !resolved_place_has_object_root_layout(values, locals, place, &resolved) {
        return None;
    }

    match classify_memory_object_ref(db, core, resolved.final_state().ty)? {
        MemoryObjectRefClass::Direct { target_ty } => Some(target_ty),
        MemoryObjectRefClass::MaterializedScalar { .. }
        | MemoryObjectRefClass::LoadedScalarHandle { .. } => None,
    }
}

pub fn runtime_shape_for_loaded_place<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
) -> Option<RuntimeShape<'db>> {
    if let Some(owner_place) = enum_tag_owner_place(place) {
        let enum_ty = place_object_ref_target_ty(db, core, values, locals, &owner_place)?;
        return enum_ty
            .as_enum(db)
            .map(|_| RuntimeShape::EnumTag { enum_ty });
    }

    let resolved = resolve_place(db, core, values, locals, place)?;
    let MemoryObjectRefClass::LoadedScalarHandle { target_ty } =
        classify_memory_object_ref(db, core, resolved.final_state().ty)?
    else {
        return None;
    };
    let info = exact_local_place_leaf_pointer_info(values, locals, place)?;
    (info.address_space == AddressSpaceKind::Memory
        && resolved_place_has_object_root_layout(values, locals, place, &resolved))
    .then_some(RuntimeShape::ObjectRef { target_ty })
}

pub fn runtime_shape_for_place_load<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    place: &Place<'db>,
) -> Option<RuntimeShape<'db>> {
    if let Some(shape) = runtime_shape_for_loaded_place(db, core, values, locals, place) {
        return Some(shape);
    }

    let resolved = resolve_place(db, core, values, locals, place)?;
    let final_state = resolved.final_state();
    let address_space = final_state
        .pointer_info
        .map(|info| info.address_space)
        .or(final_state.location_address_space())
        .or_else(|| crate::ir::try_place_address_space_in(values, locals, place))
        .unwrap_or(AddressSpaceKind::Memory);
    Some(runtime_shape_for_ty(
        db,
        core,
        final_state.ty,
        address_space,
    ))
}

pub fn runtime_shape_for_value<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    values: &[ValueData<'db>],
    locals: &[LocalData<'db>],
    value: ValueId,
) -> Option<RuntimeShape<'db>> {
    let value_data = values.get(value.index())?;
    if let crate::ir::ValueOrigin::Local(local) = value_data.origin {
        return locals.get(local.index()).map(|local| {
            if local.runtime_shape.is_unresolved() {
                runtime_shape_for_local(db, core, local)
            } else {
                local.runtime_shape
            }
        });
    }
    if let crate::ir::ValueOrigin::PlaceRoot(local) = value_data.origin {
        return locals.get(local.index()).map(|local| {
            if let Some(shape) = place_root_runtime_shape_for_local(local) {
                return shape;
            }
            if local.runtime_shape.is_unresolved() {
                runtime_shape_for_local(db, core, local)
            } else {
                local.runtime_shape
            }
        });
    }
    if let crate::ir::ValueOrigin::TransparentCast { value: inner } = value_data.origin
        && let Some(inner_shape) = runtime_shape_for_value(db, core, values, locals, inner)
        && !matches!(inner_shape, RuntimeShape::Word(_))
    {
        return Some(inner_shape);
    }
    if layout::is_zero_sized_ty(db, value_data.ty) {
        return Some(RuntimeShape::Erased);
    }
    if let Some(info) = value_data.pointer_info
        && info.address_space != AddressSpaceKind::Memory
    {
        return Some(RuntimeShape::AddressWord(info));
    }
    if let crate::ir::ValueOrigin::PlaceRef(place) | crate::ir::ValueOrigin::MoveOut { place } =
        &value_data.origin
    {
        if value_data.repr.address_space() == Some(AddressSpaceKind::Memory)
            && let Some(target_ty) = place_object_ref_target_ty(db, core, values, locals, place)
        {
            return Some(RuntimeShape::ObjectRef { target_ty });
        }
        if let Some(shape) = runtime_shape_for_loaded_place(db, core, values, locals, place) {
            return Some(shape);
        }
    }

    match value_data.repr {
        crate::ir::ValueRepr::Word => Some(RuntimeShape::Word(runtime_word_kind_for_ty(
            db,
            value_data.ty,
        ))),
        crate::ir::ValueRepr::Ref(AddressSpaceKind::Memory) => {
            if let Some(target_ty) =
                runtime_object_ref_target_ty(db, core, value_data.ty, AddressSpaceKind::Memory)
            {
                return Some(RuntimeShape::ObjectRef { target_ty });
            }

            if let Some(target_ty) = try_value_pointer_info_in(values, locals, value)
                .and_then(|info| info.target_ty)
                .filter(|target_ty| supports_object_ref_runtime_ty(db, core, *target_ty))
            {
                let target_ty = object_layout_ty(db, core, target_ty);
                match &value_data.origin {
                    crate::ir::ValueOrigin::PlaceRef(place)
                    | crate::ir::ValueOrigin::MoveOut { place }
                        if value_object_ref_target_ty(values, locals, place.base).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    crate::ir::ValueOrigin::FieldPtr(field_ptr)
                        if value_object_ref_target_ty(values, locals, field_ptr.base).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    crate::ir::ValueOrigin::TransparentCast { value: inner }
                        if value_object_ref_target_ty(values, locals, *inner).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    _ => {}
                }
            }

            Some(RuntimeShape::MemoryPtr {
                target_ty: try_value_pointer_info_in(values, locals, value)
                    .and_then(|info| info.target_ty)
                    .or(Some(value_data.ty)),
            })
        }
        crate::ir::ValueRepr::Ref(space) => Some(RuntimeShape::AddressWord(PointerInfo {
            address_space: space,
            target_ty: try_value_pointer_info_in(values, locals, value)
                .and_then(|info| info.target_ty)
                .or(Some(value_data.ty)),
        })),
        crate::ir::ValueRepr::Ptr(space) => {
            let info = try_value_pointer_info_in(values, locals, value)
                .or_else(|| runtime_value_pointer_info_for_ty(db, core, value_data.ty, space))
                .unwrap_or(PointerInfo {
                    address_space: space,
                    target_ty: None,
                });
            if let Some(target_ty) = runtime_object_ref_target_ty(db, core, value_data.ty, space) {
                return Some(RuntimeShape::ObjectRef { target_ty });
            }

            if info.address_space == AddressSpaceKind::Memory
                && effect_provider_space_for_ty(db, core, value_data.ty).is_none()
                && let Some(target_ty) = info.target_ty
                && supports_object_ref_runtime_ty(db, core, target_ty)
            {
                let target_ty = object_layout_ty(db, core, target_ty);
                match &value_data.origin {
                    crate::ir::ValueOrigin::PlaceRef(place)
                    | crate::ir::ValueOrigin::MoveOut { place }
                        if value_object_ref_target_ty(values, locals, place.base).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    crate::ir::ValueOrigin::FieldPtr(field_ptr)
                        if value_object_ref_target_ty(values, locals, field_ptr.base).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    crate::ir::ValueOrigin::TransparentCast { value: inner }
                        if value_object_ref_target_ty(values, locals, *inner).is_some() =>
                    {
                        return Some(RuntimeShape::ObjectRef { target_ty });
                    }
                    _ => {}
                }
            }

            Some(runtime_shape_for_pointer_info(info))
        }
    }
}

#[cfg(test)]
mod tests {
    use common::InputDb;
    use driver::DriverDataBase;
    use hir::analysis::ty::ty_def::TyId;
    use url::Url;

    use super::*;

    #[test]
    fn memory_scalar_place_root_refines_to_object_ref_without_pointer_metadata() {
        let mut db = DriverDataBase::default();
        let file = db.workspace().touch(
            &mut db,
            Url::parse(
                "file:///memory_scalar_place_root_refines_to_object_ref_without_pointer_metadata.fe",
            )
            .expect("test url should be valid"),
            Some("fn marker() {}".to_owned()),
        );
        let top_mod = db.top_mod(file);
        let core = CoreLib::new(&db, top_mod.scope());
        let ty = TyId::u256(&db);
        let locals = vec![LocalData {
            name: "root".to_owned(),
            ty,
            is_mut: true,
            source: crate::ir::SourceInfoId::SYNTHETIC,
            address_space: AddressSpaceKind::Memory,
            pointer_leaf_infos: Vec::new(),
            place_root_layout: LocalPlaceRootLayout::ObjectRootStorage {
                target_ty: ty,
                source: ObjectRootSource::MaterializedScalarBorrow,
            },
            runtime_shape: RuntimeShape::Unresolved,
        }];
        let values = vec![ValueData {
            ty,
            origin: crate::ir::ValueOrigin::PlaceRoot(crate::LocalId(0)),
            source: crate::ir::SourceInfoId::SYNTHETIC,
            repr: crate::ir::ValueRepr::Word,
            pointer_info: None,
            runtime_shape: RuntimeShape::Unresolved,
        }];

        assert_eq!(
            runtime_shape_for_value(&db, &core, &values, &locals, crate::ValueId(0)),
            Some(RuntimeShape::ObjectRef { target_ty: ty }),
        );
    }
}
