//! Aggregate lowering helpers for MIR: allocations, initializer emission, and type helpers.

use super::*;
use hir::{
    hir_def::{ArithBinOp, BinOp, Expr, LitKind, Partial},
    projection::{IndexSource, Projection},
};
use num_bigint::BigUint;

impl<'db, 'a> MirBuilder<'db, 'a> {
    fn try_lower_transparent_newtype_aggregate_cast(
        &mut self,
        aggregate_ty: TyId<'db>,
        fallback: ValueId,
        field_count: usize,
        inner_value: Option<ValueId>,
    ) -> Option<ValueId> {
        if crate::repr::transparent_newtype_field_ty(self.db, aggregate_ty).is_none()
            || field_count != 1
        {
            return None;
        }
        let inner_value = inner_value?;
        self.builder.body.values[fallback.index()].origin =
            ValueOrigin::TransparentCast { value: inner_value };
        self.builder.body.values[fallback.index()].repr = self.builder.body.value(inner_value).repr;
        self.refresh_value_pointer_info(fallback);
        Some(fallback)
    }

    /// Emits a fresh typed memory allocation for the given type and binds it to the expression.
    ///
    /// # Parameters
    /// - `expr`: Expression id associated with the allocation.
    ///
    /// # Returns
    /// The `ValueId` of the allocated object reference.
    pub(super) fn emit_alloc(&mut self, expr: ExprId, alloc_ty: TyId<'db>) -> ValueId {
        let value_id = self.ensure_value(expr);
        if self.current_block().is_none() {
            return value_id;
        }

        let dest = self.alloc_temp_local(alloc_ty, false, "alloc");
        self.emit_alloc_into_local(expr, dest)
    }

    pub(super) fn emit_alloc_into_local(&mut self, expr: ExprId, dest: LocalId) -> ValueId {
        let value_id = self.ensure_value(expr);
        if self.current_block().is_none() {
            return value_id;
        }

        self.set_local_address_space(dest, AddressSpaceKind::Memory);
        self.builder.body.locals[dest.index()]
            .pointer_leaf_infos
            .clear();
        let source = self.source_for_expr(expr);
        self.push_inst_here(MirInst::Assign {
            source,
            dest: Some(dest),
            rvalue: crate::ir::Rvalue::Alloc {
                address_space: AddressSpaceKind::Memory,
            },
        });
        self.builder.body.values[value_id.index()].origin = ValueOrigin::Local(dest);
        self.builder.body.values[value_id.index()].repr = ValueRepr::Ref(AddressSpaceKind::Memory);
        value_id
    }

    pub(super) fn emit_init_aggregate(
        &mut self,
        base_value: ValueId,
        inits: Vec<(MirProjectionPath<'db>, ValueId)>,
    ) {
        if inits.is_empty() {
            return;
        }
        let metadata_inits = inits.clone();
        let place = Place::new(base_value, MirProjectionPath::new());
        self.push_inst_here(MirInst::InitAggregate {
            source: self.builder.body.value(base_value).source,
            place,
            inits,
        });

        // Preserve capability pointee-space metadata for aggregate fields so
        // later loads can recover the original non-memory provider space.
        let Some((local, base_projection)) =
            crate::ir::resolve_local_projection_root(&self.builder.body.values, base_value)
        else {
            return;
        };
        let mut merged = self.builder.body.locals[local.index()]
            .pointer_leaf_infos
            .clone();
        for (init_path, init_value) in metadata_inits {
            let update_prefix = base_projection.concat(&init_path);
            merged.retain(|(path, _)| !update_prefix.is_prefix_of(path));
            for (suffix, info) in self.pointer_leaf_infos_for_value(init_value) {
                merged.push((update_prefix.concat(&suffix), info));
            }
        }
        self.builder.body.locals[local.index()].pointer_leaf_infos =
            self.normalize_pointer_leaf_infos(merged);
    }

    /// Lowers a record literal into an allocation plus `store_field` calls.
    ///
    /// # Parameters
    /// - `expr`: Record literal expression id.
    /// - `fields`: Field initializers.
    ///
    /// # Returns
    /// The value representing the allocated record.
    pub(super) fn try_lower_record(&mut self, expr: ExprId, fields: &[Field<'db>]) -> ValueId {
        let fallback = self.ensure_value(expr);
        if self.current_block().is_none() {
            return fallback;
        }
        let mut lowered_fields = Vec::with_capacity(fields.len());
        for field in fields {
            let value = self.lower_expr(field.expr);
            if self.current_block().is_none() {
                return fallback;
            }
            let Some(label) = field.label_eagerly(self.db, self.body) else {
                return fallback;
            };
            lowered_fields.push((label, value));
        }

        let record_ty = self.typed_body.expr_ty(self.db, expr);

        if let Some(value) = self.try_lower_transparent_newtype_aggregate_cast(
            record_ty,
            fallback,
            lowered_fields.len(),
            lowered_fields.first().map(|(_, value)| *value),
        ) {
            return value;
        }

        let value_id = self.emit_alloc(expr, record_ty);

        let mut inits = Vec::with_capacity(lowered_fields.len());
        for (label, field_value) in lowered_fields {
            let field_index = FieldIndex::Ident(label);
            let Some(info) = self.field_access_info(record_ty, field_index) else {
                continue;
            };
            inits.push((
                MirProjectionPath::from_projection(Projection::Field(info.field_idx)),
                field_value,
            ));
        }
        self.emit_init_aggregate(value_id, inits);

        value_id
    }

    /// Lowers a tuple literal into an allocation plus `store_field` calls.
    ///
    /// Tuples are treated as struct-like aggregates: memory is allocated for the
    /// full tuple size, and each element is stored at its computed byte offset.
    ///
    /// Transparent single-element tuples `(T,)` are represented identically to `T`, so tuple
    /// literals lower to a representation-preserving cast.
    ///
    /// # Parameters
    /// - `expr`: Tuple literal expression id.
    /// - `elems`: Element expressions.
    ///
    /// # Returns
    /// The value representing the allocated tuple.
    pub(super) fn try_lower_tuple(&mut self, expr: ExprId, elems: &[ExprId]) -> ValueId {
        let fallback = self.ensure_value(expr);
        let tuple_ty = self.typed_body.expr_ty(self.db, expr);

        // Handle unit tuple () - zero size, no allocation needed
        if tuple_ty.field_count(self.db) == 0 {
            return fallback;
        }

        // Lower all element expressions
        let mut lowered_elems = Vec::with_capacity(elems.len());
        for &elem_expr in elems {
            lowered_elems.push(self.lower_expr(elem_expr));
            if self.current_block().is_none() {
                return fallback;
            }
        }

        if let Some(value) = self.try_lower_transparent_newtype_aggregate_cast(
            tuple_ty,
            fallback,
            lowered_elems.len(),
            lowered_elems.first().copied(),
        ) {
            return value;
        }

        let value_id = self.emit_alloc(expr, tuple_ty);

        // Store each element by field index
        let mut inits = Vec::with_capacity(lowered_elems.len());
        for (i, elem_value) in lowered_elems.into_iter().enumerate() {
            inits.push((
                MirProjectionPath::from_projection(Projection::Field(i)),
                elem_value,
            ));
        }
        self.emit_init_aggregate(value_id, inits);

        value_id
    }

    /// Lowers an array literal into an allocation plus element stores.
    ///
    /// For const arrays with all compile-time constant elements:
    /// - Uses `CopyDataRegion` to efficiently copy pre-computed bytes from bytecode
    ///
    /// For arrays with non-const elements: Use alloc + InitAggregate.
    pub(super) fn try_lower_array(&mut self, expr: ExprId, elems: &[ExprId]) -> ValueId {
        let fallback = self.ensure_value(expr);
        let array_ty = self.typed_body.expr_ty(self.db, expr);
        if array_ty.generic_args(self.db).is_empty() {
            return fallback;
        }

        // Try to get the element type and determine if elements are compile-time constants
        let elem_ty = crate::layout::array_elem_ty(self.db, array_ty);
        // Use MIR memory stride so constant data matches runtime indexing rules.
        let elem_size = crate::layout::array_elem_stride_memory(self.db, array_ty);

        // Try to extract constant byte values from all elements
        if let (Some(elem_ty), Some(elem_size)) = (elem_ty, elem_size)
            && let Some(const_bytes) = self.try_extract_const_array_bytes(elems, elem_ty, elem_size)
            && self.current_block().is_some()
        {
            let region = self.builder.body.intern_const_region(array_ty, const_bytes);

            // Allocate memory and copy the constant array from code space.
            let dest = self.alloc_temp_local(array_ty, false, "array_data");
            self.set_local_address_space(dest, AddressSpaceKind::Memory);

            self.push_inst_here(MirInst::Assign {
                source: crate::ir::SourceInfoId::SYNTHETIC,
                dest: Some(dest),
                rvalue: Rvalue::Alloc {
                    address_space: AddressSpaceKind::Memory,
                },
            });

            let dest_val = self.alloc_value(
                array_ty,
                ValueOrigin::Local(dest),
                ValueRepr::Ref(AddressSpaceKind::Memory),
            );
            let dest_place = Place::new(dest_val, MirProjectionPath::new());

            let region_val = self.alloc_value(
                array_ty,
                ValueOrigin::ConstRegion(region),
                ValueRepr::Ref(AddressSpaceKind::Code),
            );

            self.push_inst_here(MirInst::Store {
                source: crate::ir::SourceInfoId::SYNTHETIC,
                place: dest_place,
                value: region_val,
            });

            self.builder.body.values[fallback.index()].origin = ValueOrigin::Local(dest);
            self.builder.body.values[fallback.index()].repr =
                ValueRepr::Ref(AddressSpaceKind::Memory);
            return fallback;
        }

        // Fall back to alloc + InitAggregate for non-const arrays
        let mut lowered_elems = Vec::with_capacity(elems.len());
        for &elem_expr in elems {
            lowered_elems.push(self.lower_expr(elem_expr));
            if self.current_block().is_none() {
                return fallback;
            }
        }

        let value_id = self.emit_alloc(expr, array_ty);

        let mut inits = Vec::with_capacity(lowered_elems.len());
        for (idx, elem_value) in lowered_elems.into_iter().enumerate() {
            let proj =
                MirProjectionPath::from_projection(Projection::Index(IndexSource::Constant(idx)));
            inits.push((proj, elem_value));
        }
        self.emit_init_aggregate(value_id, inits);

        value_id
    }

    /// Lowers an array repetition literal into an allocation plus repeated stores.
    pub(super) fn try_lower_array_rep(
        &mut self,
        expr: ExprId,
        elem: ExprId,
        len: Partial<Body<'db>>,
    ) -> ValueId {
        let fallback = self.ensure_value(expr);
        let array_ty = self.typed_body.expr_ty(self.db, expr);
        if array_ty.generic_args(self.db).is_empty() {
            return fallback;
        }

        let Some(count) =
            crate::layout::array_len_with_generic_args(self.db, array_ty, self.generic_args)
        else {
            let _ = len;
            return fallback;
        };

        let elem_value = self.lower_expr(elem);
        if self.current_block().is_none() {
            return fallback;
        }

        let value_id = self.emit_alloc(expr, array_ty);

        let mut inits = Vec::with_capacity(count);
        for idx in 0..count {
            let proj =
                MirProjectionPath::from_projection(Projection::Index(IndexSource::Constant(idx)));
            inits.push((proj, elem_value));
        }
        self.emit_init_aggregate(value_id, inits);

        value_id
    }

    pub(super) fn try_lower_dyn_string_literal(
        &mut self,
        expr: ExprId,
        literal: hir::hir_def::StringId<'db>,
    ) -> Option<ValueId> {
        let dyn_string_ty = self.typed_body.expr_ty(self.db, expr);
        if !self.is_core_dyn_string_ty(dyn_string_ty) || self.current_block().is_none() {
            return None;
        }

        let bytes = literal.data(self.db).as_bytes().to_vec();
        let len = bytes.len();
        let padded_len = len.next_multiple_of(32);
        let payload_size = 32 + padded_len;
        let payload_size_value = self.synthetic_u256(BigUint::from(payload_size));

        let ptr_local = self.alloc_temp_local(TyId::u256(self.db), false, "dyn_string_ptr");
        self.builder.body.locals[ptr_local.index()].address_space = AddressSpaceKind::Memory;
        self.assign(
            None,
            Some(ptr_local),
            Rvalue::Intrinsic {
                op: IntrinsicOp::Alloc,
                args: vec![payload_size_value],
            },
        );
        let ptr_value = self.alloc_value(
            TyId::u256(self.db),
            ValueOrigin::Local(ptr_local),
            ValueRepr::Word,
        );

        let len_value = self.synthetic_u256(BigUint::from(len));
        self.assign(
            None,
            None,
            Rvalue::Intrinsic {
                op: IntrinsicOp::Mstore,
                args: vec![ptr_value, len_value],
            },
        );

        let zero = self.synthetic_u256(BigUint::from(0u8));
        for offset in (32..payload_size).step_by(32) {
            let offset_value = self.synthetic_u256(BigUint::from(offset));
            let word_ptr = self.alloc_value(
                TyId::u256(self.db),
                ValueOrigin::Binary {
                    op: BinOp::Arith(ArithBinOp::Add),
                    lhs: ptr_value,
                    rhs: offset_value,
                },
                ValueRepr::Word,
            );
            self.assign(
                None,
                None,
                Rvalue::Intrinsic {
                    op: IntrinsicOp::Mstore,
                    args: vec![word_ptr, zero],
                },
            );
        }

        if len > 0 {
            let data_offset = self.synthetic_u256(BigUint::from(32u8));
            let data_ptr = self.alloc_value(
                TyId::u256(self.db),
                ValueOrigin::Binary {
                    op: BinOp::Arith(ArithBinOp::Add),
                    lhs: ptr_value,
                    rhs: data_offset,
                },
                ValueRepr::Word,
            );

            if len <= 32 {
                let shift = (32 - len) * 8;
                let word_value = self.synthetic_u256(BigUint::from_bytes_be(&bytes) << shift);
                self.assign(
                    None,
                    None,
                    Rvalue::Intrinsic {
                        op: IntrinsicOp::Mstore,
                        args: vec![data_ptr, word_value],
                    },
                );
            } else {
                let region = self
                    .builder
                    .body
                    .intern_const_region(TyId::u256(self.db), bytes);
                let src = self.alloc_value(
                    TyId::u256(self.db),
                    ValueOrigin::ConstRegion(region),
                    ValueRepr::Word,
                );
                self.assign(
                    None,
                    None,
                    Rvalue::Intrinsic {
                        op: IntrinsicOp::Codecopy,
                        args: vec![data_ptr, src, len_value],
                    },
                );
            }
        }

        let dyn_string = self.emit_alloc(expr, dyn_string_ty);
        let size_value = self.synthetic_u256(BigUint::from(payload_size));

        let data_ident = IdentId::new(self.db, "data".to_string());
        let len_ident = IdentId::new(self.db, "len".to_string());
        let size_ident = IdentId::new(self.db, "size".to_string());

        let data_field = self
            .field_access_info(dyn_string_ty, FieldIndex::Ident(data_ident))
            .expect("core::abi::DynString should have a `data` field");
        let len_field = self
            .field_access_info(dyn_string_ty, FieldIndex::Ident(len_ident))
            .expect("core::abi::DynString should have a `len` field");
        let size_field = self
            .field_access_info(dyn_string_ty, FieldIndex::Ident(size_ident))
            .expect("core::abi::DynString should have a `size` field");

        self.emit_init_aggregate(
            dyn_string,
            vec![
                (
                    MirProjectionPath::from_projection(Projection::Field(data_field.field_idx)),
                    ptr_value,
                ),
                (
                    MirProjectionPath::from_projection(Projection::Field(len_field.field_idx)),
                    len_value,
                ),
                (
                    MirProjectionPath::from_projection(Projection::Field(size_field.field_idx)),
                    size_value,
                ),
            ],
        );
        Some(dyn_string)
    }

    /// Returns the field type and byte offset for a given receiver/field pair.
    ///
    /// # Parameters
    /// - `owner_ty`: Type containing the field.
    /// - `field_index`: Field identifier (by name or index).
    ///
    /// # Returns
    /// Field type and offset in bytes, or `None` if the field cannot be resolved.
    pub(super) fn field_access_info(
        &self,
        owner_ty: TyId<'db>,
        field_index: FieldIndex<'db>,
    ) -> Option<FieldAccessInfo<'db>> {
        let record_like = RecordLike::from_ty(owner_ty);
        let idx = match field_index {
            FieldIndex::Ident(label) => record_like.record_field_idx(self.db, label)?,
            FieldIndex::Index(integer) => integer.data(self.db).to_usize()?,
        };
        Some(FieldAccessInfo {
            field_ty: self.field_ty_by_index(&record_like, idx)?,
            field_idx: idx,
        })
    }

    /// Computes the field type for the `idx`th field of a record-like type.
    ///
    /// # Parameters
    /// - `record_like`: Record or variant wrapper.
    /// - `idx`: Zero-based field index.
    ///
    /// # Returns
    /// The field type, or `None` if out of bounds.
    pub(super) fn field_ty_by_index(
        &self,
        record_like: &RecordLike<'db>,
        idx: usize,
    ) -> Option<TyId<'db>> {
        let ty = match record_like {
            RecordLike::Type(ty) => *ty,
            RecordLike::EnumVariant(variant) => variant.ty,
        };
        let field_types = ty.field_types(self.db);
        if idx >= field_types.len() {
            return None;
        }
        Some(field_types[idx])
    }

    /// Emits a synthetic `u256` literal value.
    ///
    /// # Parameters
    /// - `value`: Integer literal to encode.
    ///
    /// # Returns
    /// The allocated synthetic value id.
    pub(super) fn synthetic_u256(&mut self, value: BigUint) -> ValueId {
        let ty = TyId::new(self.db, TyData::TyBase(TyBase::Prim(PrimTy::U256)));
        self.builder.body.alloc_value(ValueData {
            ty,
            origin: ValueOrigin::Synthetic(SyntheticValue::Int(value)),
            source: crate::ir::SourceInfoId::SYNTHETIC,
            repr: ValueRepr::Word,
            pointer_info: None,
            runtime_shape: crate::ir::RuntimeShape::Unresolved,
        })
    }

    /// Attempts to extract constant byte values from all array elements.
    ///
    /// Returns `None` if any element is non-constant or non-integer.
    fn try_extract_const_array_bytes(
        &self,
        elems: &[ExprId],
        elem_ty: TyId<'db>,
        elem_size: usize,
    ) -> Option<Vec<u8>> {
        // Only support primitive integer types for now
        let prim_ty = match elem_ty.base_ty(self.db).data(self.db) {
            TyData::TyBase(TyBase::Prim(prim)) => prim,
            _ => return None,
        };

        let mut bytes = Vec::with_capacity(elems.len() * elem_size);

        for &elem_expr in elems {
            // Try to get the literal value
            let int_value = match elem_expr.data(self.db, self.body) {
                Partial::Present(Expr::Lit(LitKind::Int(int_id))) => int_id.data(self.db).clone(),
                _ => return None, // Non-constant or non-integer element
            };

            // Convert to bytes based on element size (big-endian, padded to EVM word)
            let int_bytes = int_value.to_bytes_be();
            let padded = self.pad_int_to_size(&int_bytes, elem_size, *prim_ty)?;
            bytes.extend(padded);
        }

        Some(bytes)
    }

    /// Pads integer bytes to the specified size for the given primitive type.
    ///
    /// Returns `None` if the value doesn't fit in the specified size.
    fn pad_int_to_size(&self, int_bytes: &[u8], size: usize, prim_ty: PrimTy) -> Option<Vec<u8>> {
        if int_bytes.len() > size {
            return None; // Value too large
        }

        let mut padded = vec![0u8; size];
        // For signed types, we'd need sign extension, but for simplicity
        // we just zero-extend (works for unsigned types)
        let offset = size - int_bytes.len();
        padded[offset..].copy_from_slice(int_bytes);

        // For signed types, check if we need sign extension
        if matches!(
            prim_ty,
            PrimTy::I8 | PrimTy::I16 | PrimTy::I32 | PrimTy::I64 | PrimTy::I128 | PrimTy::I256
        ) {
            // If the high bit of the original value is set, fill with 0xFF
            if !int_bytes.is_empty() && int_bytes[0] & 0x80 != 0 {
                for b in padded.iter_mut().take(offset) {
                    *b = 0xFF;
                }
            }
        }

        Some(padded)
    }
}
