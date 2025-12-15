//! Match lowering for MIR: converts supported `match` expressions into switches and prepares
//! enum pattern bindings using decision trees for optimized codegen.

use hir::analysis::ty::{
    decision_tree::{
        build_decision_tree, Case, DecisionTree, LeafNode, Projection, ProjectionPath,
        SwitchNode,
    },
    pattern_analysis::PatternMatrix,
    simplified_pattern::ConstructorKind,
    ty_def::InvalidCause,
};

use super::*;

impl<'db, 'a> MirBuilder<'db, 'a> {
    /// Extracts a literal `SwitchValue` from a pattern when possible.
    ///
    /// # Parameters
    /// - `pat`: Pattern id to inspect.
    ///
    /// # Returns
    /// Literal switch value or `None` when not supported.
    pub(super) fn literal_pat_value(&self, pat: PatId) -> Option<SwitchValue> {
        let Partial::Present(pat_data) = pat.data(self.db, self.body) else {
            return None;
        };

        match pat_data {
            Pat::Lit(lit) => {
                let Partial::Present(lit) = lit else {
                    return None;
                };
                match lit {
                    LitKind::Int(value) => {
                        let ty = self.typed_body.pat_ty(self.db, pat);
                        let bits = self.int_type_bits(ty)?;
                        if bits > 256 {
                            return None;
                        }
                        let literal = value.data(self.db).clone();
                        let literal_bits = literal.bits();
                        if literal_bits > bits as u64 {
                            return None;
                        }
                        Some(SwitchValue::Int(literal))
                    }
                    LitKind::Bool(value) => {
                        if !self.typed_body.pat_ty(self.db, pat).is_bool(self.db) {
                            return None;
                        }
                        Some(SwitchValue::Bool(*value))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Resolves an enum variant path within a scope.
    ///
    /// # Parameters
    /// - `path`: Path to resolve.
    /// - `scope`: Scope to use for resolution.
    ///
    /// # Returns
    /// Resolved variant metadata or `None` on failure.
    pub(super) fn resolve_enum_variant(
        &self,
        path: PathId<'db>,
        scope: ScopeId<'db>,
    ) -> Option<ResolvedVariant<'db>> {
        let res = resolve_path(
            self.db,
            path,
            scope,
            PredicateListId::empty_list(self.db),
            false,
        )
        .ok()?;
        match res {
            PathRes::EnumVariant(variant) => Some(variant),
            _ => None,
        }
    }

    /// Converts enum patterns into `MatchArmPattern` when resolvable.
    ///
    /// # Parameters
    /// - `pat`: Pattern id to inspect.
    ///
    /// # Returns
    /// Enum pattern info or `None` when not an enum pattern.
    pub(super) fn enum_pat_value(&self, pat: PatId) -> Option<MatchArmPattern> {
        let Partial::Present(pat_data) = pat.data(self.db, self.body) else {
            return None;
        };
        let scope = self.typed_body.body().unwrap().scope();

        if let Pat::Path(path, ..) = pat_data
            && let Some(path) = path.to_opt()
            && let Some(variant) = self.resolve_enum_variant(path, scope)
        {
            let enum_name = variant
                .enum_(self.db)
                .name(self.db)
                .to_opt()
                .unwrap()
                .data(self.db)
                .to_string();
            return Some(MatchArmPattern::Enum {
                variant_index: variant.variant.idx as u64,
                enum_name,
                bindings: Vec::new(),
            });
        }

        if let Pat::PathTuple(path, elem_pats) = pat_data
            && let Some(path) = path.to_opt()
            && let Some(variant) = self.resolve_enum_variant(path, scope)
        {
            let enum_name = variant
                .enum_(self.db)
                .name(self.db)
                .to_opt()
                .unwrap()
                .data(self.db)
                .to_string();

            let mut bindings = Vec::new();
            let mut offset: u64 = 0;
            for elem_pat in elem_pats {
                let elem_ty = self.typed_body.pat_ty(self.db, *elem_pat);
                let elem_size = self.ty_size_bytes(elem_ty).unwrap_or(32);

                if let Partial::Present(Pat::Path(elem_path, _)) = elem_pat.data(self.db, self.body)
                    && let Some(elem_path) = elem_path.to_opt()
                    && elem_path.is_bare_ident(self.db)
                {
                    bindings.push(PatternBinding {
                        pat_id: *elem_pat,
                        field_offset: offset,
                        value: None,
                    });
                }

                offset += elem_size;
            }

            return Some(MatchArmPattern::Enum {
                variant_index: variant.variant.idx as u64,
                enum_name,
                bindings,
            });
        }

        None
    }

    /// Returns `true` if the pattern is a wildcard (`_`).
    ///
    /// # Parameters
    /// - `pat`: Pattern id to inspect.
    ///
    /// # Returns
    /// `true` when the pattern is a wildcard.
    pub(super) fn is_wildcard_pat(&self, pat: PatId) -> bool {
        matches!(
            pat.data(self.db, self.body),
            Partial::Present(Pat::WildCard)
        )
    }

    /// Lowers a match expression using decision trees for optimized codegen.
    ///
    /// # Parameters
    /// - `block`: Entry block for the match.
    /// - `match_expr`: Expression id of the match.
    /// - `scrutinee`: Scrutinee expression id.
    /// - `arms`: Match arms to lower.
    ///
    /// # Returns
    /// Successor merge block (if any) and the value representing the match expression.
    pub(super) fn lower_match_with_decision_tree(
        &mut self,
        block: BasicBlockId,
        match_expr: ExprId,
        scrutinee: ExprId,
        arms: &[MatchArm],
    ) -> (Option<BasicBlockId>, ValueId) {
        // Lower the scrutinee to get its value
        let (scrut_block_opt, scrutinee_value) = self.lower_expr_in(block, scrutinee);
        let Some(scrut_block) = scrut_block_opt else {
            let value = self.ensure_value(match_expr);
            return (None, value);
        };

        // Build pattern matrix from match arms
        let scrutinee_ty = self.typed_body.expr_ty(self.db, scrutinee);
        let scope = self.typed_body.body().unwrap().scope();

        let patterns: Vec<Pat> = arms
            .iter()
            .filter_map(|arm| {
                if let Partial::Present(pat) = arm.pat.data(self.db, self.body) {
                    Some(pat.clone())
                } else {
                    eprintln!("DEBUG: Pattern {:?} is Absent", arm.pat);
                    None
                }
            })
            .collect();

        if patterns.len() != arms.len() {
            // Some patterns couldn't be resolved, fall back to old behavior
            eprintln!("DEBUG: pattern count {} != arm count {}, arms: {:?}",
                      patterns.len(), arms.len(), arms);
            let value = self.ensure_value(match_expr);
            return (Some(scrut_block), value);
        }

        let matrix = PatternMatrix::from_hir_patterns(
            self.db,
            &patterns,
            self.body,
            scope,
            scrutinee_ty,
        );

        // Build decision tree from pattern matrix
        let tree = build_decision_tree(self.db, &matrix);

        // Pre-lower each arm body to determine termination status and create blocks
        let mut merge_block: Option<BasicBlockId> = None;
        let mut arm_blocks = Vec::with_capacity(arms.len());
        for arm in arms {
            let arm_entry = self.alloc_block();
            let (arm_end, _) = self.lower_expr_in(arm_entry, arm.body);
            let terminates = arm_end.is_none();
            if let Some(end_block) = arm_end {
                let merge = match merge_block {
                    Some(block) => block,
                    None => {
                        let block = self.alloc_block();
                        merge_block = Some(block);
                        block
                    }
                };
                self.set_terminator(end_block, Terminator::Goto { target: merge });
            }
            arm_blocks.push((arm_entry, terminates));
        }

        // Ensure we have a merge block even if all arms terminate
        let merge_block = merge_block.unwrap_or_else(|| self.alloc_block());

        // Collect arm info for codegen (needed for match_info)
        let mut arms_info: Vec<MatchArmLowering> = arms
            .iter()
            .zip(arm_blocks.iter())
            .map(|(arm, (block_id, terminates))| {
                // Determine the pattern type for codegen
                let pattern = if self.is_wildcard_pat(arm.pat) {
                    MatchArmPattern::Wildcard
                } else if let Some(lit_val) = self.literal_pat_value(arm.pat) {
                    MatchArmPattern::Literal(lit_val)
                } else if let Some(enum_pat) = self.enum_pat_value(arm.pat) {
                    enum_pat
                } else {
                    // Fallback to wildcard for unsupported patterns
                    MatchArmPattern::Wildcard
                };

                MatchArmLowering {
                    pattern,
                    body: arm.body,
                    block: *block_id,
                    terminates: *terminates,
                    decision_tree_bindings: Vec::new(),
                }
            })
            .collect();

        // Populate decision tree bindings for tuple/struct/enum patterns.
        // Decision tree bindings handle all patterns uniformly, including nested enums.
        let leaf_bindings = self.collect_leaf_bindings(&tree);
        for (arm_idx, arm_info) in arms_info.iter_mut().enumerate() {
            if let Some(bindings) = leaf_bindings.get(&arm_idx) {
                for (name, path) in bindings {
                    let value = self.lower_projection_path_for_binding(
                        path,
                        scrutinee_value,
                        scrutinee_ty,
                        match_expr,
                    );
                    arm_info.decision_tree_bindings.push(DecisionTreeBinding {
                        name: name.clone(),
                        value,
                    });
                }
            }
        }

        // Store match info for codegen
        let has_non_terminating = arm_blocks.iter().any(|(_, terminates)| !terminates);
        self.mir_body.match_info.insert(
            match_expr,
            MatchLoweringInfo {
                scrutinee: scrutinee_value,
                merge_block: if has_non_terminating { Some(merge_block) } else { None },
                arms: arms_info,
            },
        );

        let tree_entry = self.lower_decision_tree(
            &tree,
            scrutinee_value,
            scrutinee_ty,
            &arm_blocks,
            match_expr,
            if has_non_terminating { Some(merge_block) } else { None },
        );

        // Set scrut_block to jump to the tree entry
        self.set_terminator(scrut_block, Terminator::Goto { target: tree_entry });

        let value_id = self.ensure_value(match_expr);
        (Some(merge_block), value_id)
    }

    /// Recursively lowers a decision tree to MIR basic blocks.
    ///
    /// # Parameters
    /// - `tree`: Decision tree node to lower.
    /// - `scrutinee_value`: Value representing the root scrutinee.
    /// - `scrutinee_ty`: Type of the scrutinee.
    /// - `arm_blocks`: Pre-created blocks and termination status for each arm.
    /// - `match_expr`: The match expression id.
    /// - `merge_block`: Optional merge block for match results.
    ///
    /// # Returns
    /// The entry basic block for this tree node.
    fn lower_decision_tree(
        &mut self,
        tree: &DecisionTree<'db>,
        scrutinee_value: ValueId,
        scrutinee_ty: TyId<'db>,
        arm_blocks: &[(BasicBlockId, bool)],
        match_expr: ExprId,
        merge_block: Option<BasicBlockId>,
    ) -> BasicBlockId {
        match tree {
            DecisionTree::Leaf(leaf) => {
                self.lower_leaf_node(leaf, arm_blocks)
            }
            DecisionTree::Switch(switch_node) => {
                self.lower_switch_node(
                    switch_node,
                    scrutinee_value,
                    scrutinee_ty,
                    arm_blocks,
                    match_expr,
                    merge_block,
                )
            }
        }
    }

    /// Lowers a leaf node (match arm execution) to the pre-created arm block.
    fn lower_leaf_node(
        &mut self,
        leaf: &LeafNode<'db>,
        arm_blocks: &[(BasicBlockId, bool)],
    ) -> BasicBlockId {
        // Return the pre-created block for this arm
        // The arm body was already lowered during the pre-lowering phase
        let (arm_block, _terminates) = arm_blocks[leaf.arm_index];
        arm_block
    }

    /// Lowers a switch node (test and branch) to MIR basic blocks.
    fn lower_switch_node(
        &mut self,
        switch_node: &SwitchNode<'db>,
        scrutinee_value: ValueId,
        scrutinee_ty: TyId<'db>,
        arm_blocks: &[(BasicBlockId, bool)],
        match_expr: ExprId,
        merge_block: Option<BasicBlockId>,
    ) -> BasicBlockId {
        // For Type constructors (tuples/structs), there's no discriminant to switch on.
        // We skip straight to the subtree and let the inner switches handle the actual values.
        let is_structural_only = switch_node.arms.iter().all(|(case, _)| {
            matches!(case, Case::Constructor(ConstructorKind::Type(_)) | Case::Default)
        });

        if is_structural_only && !switch_node.arms.is_empty() {
            // Find the structural subtree to descend into
            let structural_subtree = switch_node.arms.iter()
                .find(|(case, _)| matches!(case, Case::Constructor(ConstructorKind::Type(_))))
                .or_else(|| switch_node.arms.iter().find(|(case, _)| matches!(case, Case::Default)))
                .map(|(_, subtree)| subtree);

            if let Some(subtree) = structural_subtree {
                // For structural types, directly lower the subtree - no switch needed at this level
                return self.lower_decision_tree(
                    subtree,
                    scrutinee_value,
                    scrutinee_ty,
                    arm_blocks,
                    match_expr,
                    merge_block,
                );
            }
        }

        let test_block = self.alloc_block();

        // Extract the value to test based on the occurrence path
        let test_value = self.lower_occurrence(&switch_node.occurrence, scrutinee_value, scrutinee_ty, match_expr);

        // Recursively lower each case
        let mut targets = vec![];
        let mut default_block = None;

        for (case, subtree) in &switch_node.arms {
            let subtree_entry = self.lower_decision_tree(
                subtree,
                scrutinee_value,
                scrutinee_ty,
                arm_blocks,
                match_expr,
                merge_block,
            );

            match case {
                Case::Constructor(ctor) => {
                    if let Some(switch_val) = self.constructor_to_switch_value(ctor) {
                        targets.push(SwitchTarget {
                            value: switch_val,
                            block: subtree_entry,
                        });
                    }
                }
                Case::Default => {
                    default_block = Some(subtree_entry);
                }
            }
        }

        let default = default_block.unwrap_or_else(|| {
            let unreachable = self.alloc_block();
            self.set_terminator(unreachable, Terminator::Unreachable);
            unreachable
        });

        // Always use MatchExpr origin for all switches in a decision tree match.
        // This ensures emit_match_switch is called, which reuses the same match temp
        // via match_values.entry(expr_id). All switches in the same match share
        // the same temp variable for collecting results.
        let origin = SwitchOrigin::MatchExpr(match_expr);

        self.set_terminator(
            test_block,
            Terminator::Switch {
                discr: test_value,
                targets,
                default,
                origin,
            },
        );

        test_block
    }

    /// Extracts a value from the scrutinee based on a projection path.
    ///
    /// Handles both Field steps (for tuple/struct access) and VariantField steps
    /// (for accessing data inside matched enum variants).
    fn lower_occurrence(
        &mut self,
        path: &ProjectionPath<'db>,
        scrutinee_value: ValueId,
        scrutinee_ty: TyId<'db>,
        match_expr: ExprId,
    ) -> ValueId {
        // Traverse the projection path, extracting each field in sequence
        let mut current_value = scrutinee_value;
        let mut current_ty = scrutinee_ty;

        for step in path.iter() {
            match step {
                Projection::Field(field_idx) => {
                    // Regular field access (tuple/struct)
                    let record_like = RecordLike::from_ty(current_ty);
                    let Some((field_ty, offset_bytes)) =
                        self.field_layout_by_index(&record_like, *field_idx)
                    else {
                        break;
                    };

                    let addr_space = self.value_address_space(current_value);
                    let is_aggregate = field_ty.field_count(self.db) > 0;

                    if is_aggregate {
                        if offset_bytes == 0 {
                            self.value_address_space.insert(current_value, addr_space);
                        } else {
                            current_value = self.mir_body.alloc_value(ValueData {
                                ty: field_ty,
                                origin: ValueOrigin::FieldPtr(FieldPtrOrigin {
                                    base: current_value,
                                    offset_bytes,
                                }),
                            });
                            self.value_address_space.insert(current_value, addr_space);
                        }
                    } else {
                        let ptr_ty = match addr_space {
                            AddressSpaceKind::Memory => self.core.helper_ty(CoreHelperTy::MemPtr),
                            AddressSpaceKind::Storage => self.core.helper_ty(CoreHelperTy::StorPtr),
                        };
                        let offset_value = self.synthetic_u256(BigUint::from(offset_bytes));
                        let callable = self.core.make_callable(
                            match_expr,
                            CoreHelper::GetField,
                            &[ptr_ty, field_ty],
                        );

                        current_value = self.mir_body.alloc_value(ValueData {
                            ty: field_ty,
                            origin: ValueOrigin::Call(CallOrigin {
                                expr: match_expr,
                                callable,
                                args: vec![current_value, offset_value],
                                receiver_space: None,
                                resolved_name: None,
                            }),
                        });
                    }

                    current_ty = field_ty;
                }

                Projection::VariantField {
                    variant,
                    enum_ty,
                    field_idx,
                } => {
                    // Variant field access - use GetVariantField
                    let ctor = ConstructorKind::Variant(*variant, *enum_ty);
                    let field_types = ctor.field_types(self.db);
                    let field_ty = field_types
                        .get(*field_idx)
                        .copied()
                        .unwrap_or_else(|| TyId::invalid(self.db, InvalidCause::Other));
                    let offset_bytes = self.compute_variant_field_offset_from_types(&field_types, *field_idx);

                    let addr_space = self.value_address_space(current_value);
                    let is_aggregate = field_ty.field_count(self.db) > 0;

                    if is_aggregate {
                        // For aggregate variant fields, just compute the offset
                        if offset_bytes == 0 {
                            self.value_address_space.insert(current_value, addr_space);
                        } else {
                            current_value = self.mir_body.alloc_value(ValueData {
                                ty: field_ty,
                                origin: ValueOrigin::FieldPtr(FieldPtrOrigin {
                                    base: current_value,
                                    offset_bytes,
                                }),
                            });
                            self.value_address_space.insert(current_value, addr_space);
                        }
                    } else {
                        let ptr_ty = match addr_space {
                            AddressSpaceKind::Memory => self.core.helper_ty(CoreHelperTy::MemPtr),
                            AddressSpaceKind::Storage => self.core.helper_ty(CoreHelperTy::StorPtr),
                        };
                        let offset_value = self.synthetic_u256(BigUint::from(offset_bytes));
                        let callable = self.core.make_callable(
                            match_expr,
                            CoreHelper::GetVariantField,
                            &[ptr_ty, field_ty],
                        );

                        current_value = self.mir_body.alloc_value(ValueData {
                            ty: field_ty,
                            origin: ValueOrigin::Call(CallOrigin {
                                expr: match_expr,
                                callable,
                                args: vec![current_value, offset_value],
                                receiver_space: None,
                                resolved_name: None,
                            }),
                        });
                    }

                    current_ty = field_ty;
                }
            }
        }

        // For enums, extract the discriminant for switching
        let (base_ty, _) = current_ty.decompose_ty_app(self.db);
        if let TyData::TyBase(TyBase::Adt(adt_def)) = base_ty.data(self.db) {
            if matches!(adt_def.adt_ref(self.db), AdtRef::Enum(_)) {
                let ptr_ty = match self.value_address_space(current_value) {
                    AddressSpaceKind::Memory => self.core.helper_ty(CoreHelperTy::MemPtr),
                    AddressSpaceKind::Storage => self.core.helper_ty(CoreHelperTy::StorPtr),
                };
                let callable = self.core.make_callable(
                    match_expr,
                    CoreHelper::GetDiscriminant,
                    &[ptr_ty],
                );
                let ty = callable.ret_ty(self.db);
                return self.mir_body.alloc_value(ValueData {
                    ty,
                    origin: ValueOrigin::Call(CallOrigin {
                        expr: match_expr,
                        callable,
                        args: vec![current_value],
                        receiver_space: None,
                        resolved_name: None,
                    }),
                });
            }
        }

        current_value
    }

    /// Converts a constructor to a switch value for MIR.
    fn constructor_to_switch_value(&self, ctor: &ConstructorKind<'db>) -> Option<SwitchValue> {
        match ctor {
            ConstructorKind::Variant(variant, _) => {
                Some(SwitchValue::Enum(variant.idx as u64))
            }
            ConstructorKind::Literal(lit, _) => match lit {
                LitKind::Int(value) => Some(SwitchValue::Int(value.data(self.db).clone())),
                LitKind::Bool(value) => Some(SwitchValue::Bool(*value)),
                _ => None,
            },
            ConstructorKind::Type(_) => None,
        }
    }

    /// Extracts a value from the scrutinee for binding purposes.
    ///
    /// Creates a Place with the projection path and uses PlaceLoad for scalars
    /// or PlaceRef for aggregates.
    fn lower_projection_path_for_binding(
        &mut self,
        path: &ProjectionPath<'db>,
        scrutinee_value: ValueId,
        scrutinee_ty: TyId<'db>,
        _match_expr: ExprId,
    ) -> ValueId {
        // Empty path means we bind to the scrutinee itself
        if path.is_empty() {
            return scrutinee_value;
        }

        // Compute the final type by walking the projection path
        let final_ty = self.compute_projection_result_type(scrutinee_ty, path);
        let is_aggregate = final_ty.field_count(self.db) > 0;

        // Track address space for the result
        let addr_space = self.value_address_space(scrutinee_value);

        // Create the Place
        let place = Place {
            base: scrutinee_value,
            projection: path.clone(),
            address_space: addr_space,
        };

        // Use PlaceRef for aggregates (pointer only), PlaceLoad for scalars (load value)
        let origin = if is_aggregate {
            ValueOrigin::PlaceRef(place)
        } else {
            ValueOrigin::PlaceLoad(place)
        };

        let value_id = self.mir_body.alloc_value(ValueData {
            ty: final_ty,
            origin,
        });

        self.value_address_space.insert(value_id, addr_space);
        value_id
    }

    /// Computes the result type of applying a projection path to a type.
    fn compute_projection_result_type(
        &self,
        base_ty: TyId<'db>,
        path: &ProjectionPath<'db>,
    ) -> TyId<'db> {
        let mut current_ty = base_ty;

        for proj in path.iter() {
            match proj {
                Projection::Field(field_idx) => {
                    let field_types = current_ty.field_types(self.db);
                    if let Some(&field_ty) = field_types.get(*field_idx) {
                        current_ty = field_ty;
                    }
                }
                Projection::VariantField {
                    variant,
                    enum_ty,
                    field_idx,
                } => {
                    let ctor = ConstructorKind::Variant(*variant, *enum_ty);
                    let field_types = ctor.field_types(self.db);
                    if let Some(&field_ty) = field_types.get(*field_idx) {
                        current_ty = field_ty;
                    }
                }
            }
        }

        current_ty
    }

    /// Computes the byte offset for a variant's field using pre-computed field types.
    fn compute_variant_field_offset_from_types(&self, field_types: &[TyId<'db>], field_idx: usize) -> u64 {
        let mut offset = 0u64;
        for i in 0..field_idx {
            if let Some(&field_ty) = field_types.get(i) {
                offset += self.ty_size_bytes(field_ty).unwrap_or(32);
            }
        }
        offset
    }

    /// Collects all bindings from decision tree leaves, grouped by arm index.
    ///
    /// Returns a map from arm_index to a list of (variable_name, projection_path) pairs.
    fn collect_leaf_bindings(
        &self,
        tree: &DecisionTree<'db>,
    ) -> FxHashMap<usize, Vec<(String, ProjectionPath<'db>)>> {
        let mut bindings_by_arm: FxHashMap<usize, Vec<(String, ProjectionPath<'db>)>> =
            FxHashMap::default();
        self.collect_leaf_bindings_recursive(tree, &mut bindings_by_arm);
        bindings_by_arm
    }

    fn collect_leaf_bindings_recursive(
        &self,
        tree: &DecisionTree<'db>,
        bindings_by_arm: &mut FxHashMap<usize, Vec<(String, ProjectionPath<'db>)>>,
    ) {
        match tree {
            DecisionTree::Leaf(leaf) => {
                let arm_bindings = bindings_by_arm.entry(leaf.arm_index).or_default();
                for ((ident_id, _), path) in &leaf.bindings {
                    let name = ident_id.data(self.db).to_string();
                    // Only add if we don't already have this name for this arm
                    if !arm_bindings.iter().any(|(n, _)| n == &name) {
                        arm_bindings.push((name, path.clone()));
                    }
                }
            }
            DecisionTree::Switch(switch_node) => {
                for (_, subtree) in &switch_node.arms {
                    self.collect_leaf_bindings_recursive(subtree, bindings_by_arm);
                }
            }
        }
    }
}
