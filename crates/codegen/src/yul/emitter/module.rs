//! Module-level Yul emission helpers (functions + code regions).

use common::{
    InputDb,
    ingot::{Ingot, IngotKind},
};
use driver::DriverDataBase;
use hir::HirDb;
use hir::analysis::HirAnalysisDb;
use hir::analysis::ty::ty_def::{PrimTy, TyBase, TyData};
use hir::hir_def::{HirIngot, ItemKind, TopLevelMod};
use mir::analysis::{
    CallGraph, ContractRegion, ContractRegionKind, build_call_graph, build_contract_graph,
    reachable_functions,
};
use mir::{
    MirFunction, MirInst, MirModule, Rvalue, ValueOrigin,
    ir::{IntrinsicOp, MirFunctionOrigin, SymbolSource},
    layout::{self, TargetDataLayout},
    lower_ingot, lower_module, prepare_module_for_evm_yul_codegen,
};
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use std::{collections::VecDeque, sync::Arc};

use crate::yul::doc::{YulDoc, render_docs};
use crate::yul::errors::YulError;

use super::{
    EmitModuleError,
    function::{FunctionEmitter, YulDataRegion},
    util::{function_name, prefix_yul_name},
};

/// Metadata describing a single emitted test object.
#[derive(Debug, Clone)]
pub struct TestMetadata {
    pub display_name: String,
    pub hir_name: String,
    pub symbol_name: String,
    pub object_name: String,
    pub yul: String,
    /// Backend-produced init bytecode (used by the Sonatina `fe test` backend).
    ///
    /// When emitting Yul, this is left empty and the runner compiles `yul` via `solc`.
    pub bytecode: Vec<u8>,
    /// Optional Sonatina object-level observability JSON snapshot.
    pub sonatina_observability_json: Option<String>,
    pub value_param_count: usize,
    pub effect_param_count: usize,
    pub expected_revert: Option<ExpectedRevert>,
    /// Optional initial ETH balance (in wei) to seed the deployed test contract.
    /// When `None`, the contract starts with zero balance.
    pub initial_balance: Option<Vec<u8>>,
}

/// Describes the expected revert behavior for a test.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectedRevert {
    /// Test should revert with any data.
    Any,
    /// Test should revert with data starting with the given 4-byte selector.
    Selector([u8; 4]),
    /// Test should revert with a Panic(uint256) whose code matches.
    /// Stores the expected full revert payload: selector (4 bytes) + ABI-encoded code (32 bytes).
    PanicCode(Vec<u8>),
}

/// Output returned by `emit_test_module_yul`.
#[derive(Debug, Clone)]
pub struct TestModuleOutput {
    pub tests: Vec<TestMetadata>,
}

/// Emits Yul for every function in the lowered MIR module.
///
/// * `db` - Driver database used to query compiler facts.
/// * `top_mod` - Root module to lower.
///
/// Returns a single Yul string containing all lowered functions followed by any
/// auto-generated code regions, or [`EmitModuleError`] if MIR lowering or Yul
/// emission fails.
pub fn emit_module_yul(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
) -> Result<String, EmitModuleError> {
    emit_module_yul_with_layout(db, top_mod, layout::EVM_LAYOUT)
}

pub fn emit_module_yul_with_layout(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
    layout: TargetDataLayout,
) -> Result<String, EmitModuleError> {
    let mut module = lower_module(db, top_mod).map_err(EmitModuleError::MirLower)?;
    link_yul_numeric_intrinsic_helpers(db, &mut module)?;
    prepare_module_for_evm_yul_codegen(db, &mut module);
    emit_lowered_module_yul_with_layout(db, &module, layout)
}

/// Emits Yul for every function in an ingot (across all source files).
pub fn emit_ingot_yul(db: &DriverDataBase, ingot: Ingot<'_>) -> Result<String, EmitModuleError> {
    emit_ingot_yul_with_layout(db, ingot, layout::EVM_LAYOUT)
}

pub fn emit_ingot_yul_with_layout(
    db: &DriverDataBase,
    ingot: Ingot<'_>,
    layout: TargetDataLayout,
) -> Result<String, EmitModuleError> {
    let mut module = lower_ingot(db, ingot).map_err(EmitModuleError::MirLower)?;
    link_yul_numeric_intrinsic_helpers(db, &mut module)?;
    prepare_module_for_evm_yul_codegen(db, &mut module);
    emit_lowered_module_yul_with_layout(db, &module, layout)
}

fn emit_lowered_module_yul_with_layout(
    db: &DriverDataBase,
    module: &MirModule<'_>,
    layout: TargetDataLayout,
) -> Result<String, EmitModuleError> {
    let contract_graph = build_contract_graph(&module.functions);

    let mut code_regions = FxHashMap::default();
    for (name, entry) in &contract_graph.contracts {
        if let Some(init) = &entry.init_symbol {
            code_regions.insert(init.clone(), name.clone());
        }
        if let Some(runtime) = &entry.deployed_symbol {
            code_regions.insert(runtime.clone(), format!("{name}_deployed"));
        }
    }
    let code_region_roots = collect_code_region_roots(db, &module.functions);
    for root in &code_region_roots {
        if code_regions.contains_key(root) {
            continue;
        }
        code_regions
            .entry(root.clone())
            .or_insert_with(|| format!("code_region_{}", sanitize_symbol(root)));
    }
    let code_regions = Arc::new(code_regions);

    // Emit Yul docs for each function
    let mut function_docs: Vec<(Vec<YulDoc>, Vec<YulDataRegion>)> =
        Vec::with_capacity(module.functions.len());
    for func in module.functions.iter() {
        let emitter =
            FunctionEmitter::new(db, func, &code_regions, layout).map_err(EmitModuleError::Yul)?;
        let is_test = match func.origin {
            MirFunctionOrigin::Hir(hir_func) => ItemKind::from(hir_func)
                .attrs(db)
                .is_some_and(|attrs| attrs.has_attr(db, "test")),
            MirFunctionOrigin::Synthetic(_) => false,
        };
        if is_test {
            validate_test_function(db, func, emitter.returns_value())?;
        }
        let (docs, data_regions) = emitter.emit_doc().map_err(EmitModuleError::Yul)?;
        function_docs.push((docs, data_regions));
    }

    // Index function docs by symbol for region assembly.
    let mut docs_by_symbol = FxHashMap::default();
    for (idx, func) in module.functions.iter().enumerate() {
        let (docs, data_regions) = &function_docs[idx];
        docs_by_symbol.insert(
            func.symbol_name.clone(),
            FunctionDocInfo {
                docs: docs.clone(),
                data_regions: data_regions.clone(),
            },
        );
    }

    let mut contract_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut referenced_contracts = FxHashSet::default();
    for (from_region, deps) in &contract_graph.region_deps {
        for dep in deps {
            if dep.contract_name != from_region.contract_name {
                referenced_contracts.insert(dep.contract_name.clone());
                contract_deps
                    .entry(from_region.contract_name.clone())
                    .or_default()
                    .insert(dep.contract_name.clone());
            }
        }
    }

    let mut root_contracts: Vec<_> = contract_graph
        .contracts
        .keys()
        .filter(|name| !referenced_contracts.contains(*name))
        .cloned()
        .collect();
    root_contracts.sort();

    // Ensure the contract dependency graph is rooted; otherwise we'd silently omit contracts or
    // fall back to emitting raw functions (which breaks `dataoffset/datasize` scoping).
    if !contract_graph.contracts.is_empty() {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        for name in &root_contracts {
            queue.push_back(name.clone());
        }
        while let Some(name) = queue.pop_front() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if let Some(deps) = contract_deps.get(&name) {
                for dep in deps {
                    queue.push_back(dep.clone());
                }
            }
        }
        if visited.len() != contract_graph.contracts.len() {
            let mut missing: Vec<_> = contract_graph
                .contracts
                .keys()
                .filter(|name| !visited.contains(*name))
                .cloned()
                .collect();
            missing.sort();
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "contract region graph is not rooted (cycle likely); unreachable contracts: {}",
                missing.join(", ")
            ))));
        }
    }

    let mut docs = Vec::new();
    for name in root_contracts {
        let mut stack = Vec::new();
        docs.push(
            emit_contract_init_object(&name, &contract_graph, &docs_by_symbol, &mut stack)
                .map_err(EmitModuleError::Yul)?,
        );
    }

    // Free-function code regions not tied to contract entrypoints.
    let call_graph = build_call_graph(&module.functions);
    for root in code_region_roots {
        if contract_graph.symbol_to_region.contains_key(&root) {
            continue;
        }
        let Some(label) = code_regions.get(&root) else {
            continue;
        };
        let reachable = reachable_functions(&call_graph, &root);
        let mut region_docs = Vec::new();
        let mut data_regions = Vec::new();
        let mut seen_labels = FxHashSet::default();
        let mut symbols: Vec<_> = reachable.into_iter().collect();
        symbols.sort();
        for symbol in symbols {
            if let Some(info) = docs_by_symbol.get(&symbol) {
                region_docs.extend(info.docs.clone());
                for dr in &info.data_regions {
                    if seen_labels.insert(dr.label.clone()) {
                        data_regions.push(dr.clone());
                    }
                }
            }
        }
        let mut components = vec![YulDoc::block("code ", region_docs)];
        components.extend(emit_data_sections(&data_regions));
        docs.push(YulDoc::block(format!("object \"{label}\" "), components));
    }

    // If nothing was emitted (no regions), fall back to top-level functions.
    if docs.is_empty() {
        // Collect all data regions from all functions
        let mut all_data_regions = Vec::new();
        let mut seen_labels = FxHashSet::default();
        for info in docs_by_symbol.values() {
            for dr in &info.data_regions {
                if seen_labels.insert(dr.label.clone()) {
                    all_data_regions.push(dr.clone());
                }
            }
        }
        for (func_docs, _) in function_docs {
            docs.extend(func_docs);
        }
        // If there are data regions but no contract objects, we need to wrap in an object
        if !all_data_regions.is_empty() {
            let mut components = vec![YulDoc::block("code ", docs)];
            components.extend(emit_data_sections(&all_data_regions));
            docs = vec![YulDoc::block("object \"main\" ", components)];
        }
    }

    let mut lines = Vec::new();
    render_docs(&docs, 0, &mut lines);
    Ok(join_lines(lines))
}

/// Emits Yul objects that can execute `#[test]` functions directly.
///
/// * `db` - Driver database used to query compiler facts.
/// * `top_mod` - Root module to lower.
///
/// Returns test Yul output plus metadata mapping display names to test objects.
pub fn emit_test_module_yul(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
    filter: Option<&str>,
) -> Result<TestModuleOutput, EmitModuleError> {
    emit_test_module_yul_with_layout(db, top_mod, filter, layout::EVM_LAYOUT)
}

pub fn emit_test_module_yul_with_layout(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
    filter: Option<&str>,
    layout: TargetDataLayout,
) -> Result<TestModuleOutput, EmitModuleError> {
    let ingot = top_mod.ingot(db);
    let mut module = lower_ingot(db, ingot).map_err(EmitModuleError::MirLower)?;
    link_yul_numeric_intrinsic_helpers(db, &mut module)?;
    prepare_module_for_evm_yul_codegen(db, &mut module);

    let contract_graph = build_contract_graph(&module.functions);

    let mut code_regions = FxHashMap::default();
    for (name, entry) in &contract_graph.contracts {
        if let Some(init) = &entry.init_symbol {
            code_regions.insert(init.clone(), name.clone());
        }
        if let Some(runtime) = &entry.deployed_symbol {
            code_regions.insert(runtime.clone(), format!("{name}_deployed"));
        }
    }
    let code_region_roots = collect_code_region_roots(db, &module.functions);
    for root in &code_region_roots {
        if code_regions.contains_key(root) {
            continue;
        }
        code_regions
            .entry(root.clone())
            .or_insert_with(|| format!("code_region_{}", sanitize_symbol(root)));
    }
    let code_regions = Arc::new(code_regions);

    let call_graph = build_call_graph(&module.functions);
    let tests = collect_test_infos(db, &module.functions, filter)?;
    if tests.is_empty() {
        return Ok(TestModuleOutput { tests: Vec::new() });
    }
    let test_symbols: FxHashSet<_> = tests.iter().map(|test| test.symbol_name.clone()).collect();
    let funcs_by_symbol = build_funcs_by_symbol(&module.functions);
    let test_deps: Vec<_> = tests
        .iter()
        .map(|test| {
            collect_test_dependencies(
                &funcs_by_symbol,
                &call_graph,
                &contract_graph,
                &test.symbol_name,
                &test_symbols,
            )
        })
        .collect();
    let mut needed_symbols = FxHashSet::default();
    for (test, deps) in tests.iter().zip(test_deps.iter()) {
        needed_symbols.extend(reachable_functions(&call_graph, &test.symbol_name));
        for root in &deps.code_region_roots {
            needed_symbols.extend(reachable_functions(&call_graph, root));
        }
        for (region, reachable) in &contract_graph.region_reachable {
            if deps.contracts.contains(&region.contract_name) {
                needed_symbols.extend(reachable.iter().cloned());
            }
        }
    }

    let mut docs_by_symbol = FxHashMap::default();
    for func in module
        .functions
        .iter()
        .filter(|func| needed_symbols.contains(&func.symbol_name))
    {
        let emitter =
            FunctionEmitter::new(db, func, &code_regions, layout).map_err(EmitModuleError::Yul)?;
        if test_symbols.contains(&func.symbol_name) {
            validate_test_function(db, func, emitter.returns_value())?;
        }
        let (docs, data_regions) = emitter.emit_doc().map_err(EmitModuleError::Yul)?;
        docs_by_symbol.insert(
            func.symbol_name.clone(),
            FunctionDocInfo { docs, data_regions },
        );
    }

    let mut output_tests = Vec::new();
    for (test, deps) in tests.into_iter().zip(test_deps) {
        let contract_docs = emit_contract_docs(&contract_graph, &docs_by_symbol, &deps.contracts)?;
        let code_region_docs = emit_code_region_docs(
            &call_graph,
            &deps.code_region_roots,
            &contract_graph,
            &code_regions,
            &docs_by_symbol,
            &test_symbols,
        );
        let mut dependency_docs = Vec::new();
        dependency_docs.extend(contract_docs);
        dependency_docs.extend(code_region_docs);
        let doc = emit_test_object(&call_graph, &docs_by_symbol, &dependency_docs, &test)?;
        let mut lines = Vec::new();
        render_docs(std::slice::from_ref(&doc), 0, &mut lines);
        let yul = join_lines(lines);
        output_tests.push(TestMetadata {
            display_name: test.display_name,
            hir_name: test.hir_name,
            symbol_name: test.symbol_name,
            object_name: test.object_name,
            yul,
            bytecode: Vec::new(),
            sonatina_observability_json: None,
            value_param_count: test.value_param_count,
            effect_param_count: test.effect_param_count,
            expected_revert: test.expected_revert,
            initial_balance: test.initial_balance.map(|b| b.to_bytes_be()),
        });
    }

    Ok(TestModuleOutput {
        tests: output_tests,
    })
}

/// Joins rendered lines while trimming trailing whitespace-only entries.
///
/// * `lines` - Vector of rendered Yul lines.
///
/// Returns the normalized Yul output string.
fn join_lines(mut lines: Vec<String>) -> String {
    while lines.last().is_some_and(|line| line.is_empty()) {
        lines.pop();
    }
    lines.join("\n")
}

/// Collects all function symbols referenced by `code_region` intrinsics, contract
/// entrypoints, and `#[test]` functions.
///
/// * `db` - HIR database used to read attributes.
/// * `functions` - Monomorphized MIR functions to scan.
///
/// Returns a sorted list of symbol names that define code-region roots.
fn collect_code_region_roots(db: &dyn HirDb, functions: &[MirFunction<'_>]) -> Vec<String> {
    let mut roots = FxHashSet::default();
    for func in functions {
        // Contract entrypoints are code region roots
        if func.contract_function.is_some() {
            roots.insert(func.symbol_name.clone());
        }

        // #[test] functions are code region roots
        if let MirFunctionOrigin::Hir(hir_func) = func.origin
            && ItemKind::from(hir_func)
                .attrs(db)
                .is_some_and(|attrs| attrs.has_attr(db, "test"))
        {
            roots.insert(func.symbol_name.clone());
        }

        // Functions referenced by code_region intrinsics are roots
        for block in &func.body.blocks {
            for inst in &block.insts {
                if let mir::MirInst::Assign {
                    rvalue: mir::Rvalue::Intrinsic { op, args },
                    ..
                } = inst
                    && matches!(
                        *op,
                        mir::ir::IntrinsicOp::CodeRegionOffset
                            | mir::ir::IntrinsicOp::CodeRegionLen
                    )
                    && args.len() == 1
                    && let Some(arg) = args.first().copied()
                    && let mir::ValueOrigin::CodeRegionRef(target) = &func.body.value(arg).origin
                    && let Some(symbol) = &target.symbol
                {
                    roots.insert(symbol.clone());
                }
            }
        }
    }
    let mut out: Vec<_> = roots.into_iter().collect();
    out.sort();
    out
}

/// Replace any non-alphanumeric characters with `_` so the label is a valid Yul identifier.
///
/// * `component` - Raw symbol component to sanitize.
///
/// Returns a sanitized string suitable for use as a Yul identifier.
fn sanitize_symbol(component: &str) -> String {
    component
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect()
}

fn link_yul_numeric_intrinsic_helpers<'db>(
    db: &'db DriverDataBase,
    module: &mut mir::MirModule<'db>,
) -> Result<(), EmitModuleError> {
    fn integral_ty_suffix<'db>(
        db: &'db DriverDataBase,
        ty: hir::analysis::ty::ty_def::TyId<'db>,
        label: &str,
    ) -> Result<&'static str, EmitModuleError> {
        let base_ty = ty.base_ty(db);
        let TyData::TyBase(TyBase::Prim(prim)) = base_ty.data(db) else {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "{label} type must be primitive integral, got `{}`",
                ty.pretty_print(db),
            ))));
        };
        match prim {
            PrimTy::U8 => Ok("u8"),
            PrimTy::U16 => Ok("u16"),
            PrimTy::U32 => Ok("u32"),
            PrimTy::U64 => Ok("u64"),
            PrimTy::U128 => Ok("u128"),
            PrimTy::U256 => Ok("u256"),
            PrimTy::Usize => Ok("usize"),
            PrimTy::I8 => Ok("i8"),
            PrimTy::I16 => Ok("i16"),
            PrimTy::I32 => Ok("i32"),
            PrimTy::I64 => Ok("i64"),
            PrimTy::I128 => Ok("i128"),
            PrimTy::I256 => Ok("i256"),
            PrimTy::Isize => Ok("isize"),
            _ => Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "{label} type must be integral, got `{}`",
                ty.pretty_print(db),
            )))),
        }
    }

    fn helper_symbol_from_checked_intrinsic<'db>(
        db: &'db DriverDataBase,
        intrinsic: mir::ir::CheckedIntrinsic<'db>,
    ) -> Result<String, EmitModuleError> {
        let suffix = integral_ty_suffix(db, intrinsic.ty, "checked arithmetic helper")?;
        Ok(format!(
            "{}_{}",
            intrinsic.op.helper_symbol_prefix(),
            suffix
        ))
    }

    fn helper_symbol_from_saturating_intrinsic<'db>(
        db: &'db DriverDataBase,
        call: &mir::CallOrigin<'db>,
    ) -> Result<Option<String>, EmitModuleError> {
        let Some(mir::ir::CallTargetRef::Hir(target)) = call.target.as_ref() else {
            return Ok(None);
        };
        match target.callable_def.ingot(db).kind(db) {
            IngotKind::Core | IngotKind::Std => {}
            _ => return Ok(None),
        }

        let hir::hir_def::CallableDef::Func(func) = target.callable_def else {
            return Ok(None);
        };
        if func.body(db).is_some() {
            return Ok(None);
        }

        let Some(name) = target.callable_def.name(db) else {
            return Ok(None);
        };
        let prefix = match name.data(db).as_str() {
            "__saturating_add" => "saturating_add",
            "__saturating_sub" => "saturating_sub",
            "__saturating_mul" => "saturating_mul",
            _ => return Ok(None),
        };
        let [ty] = target.generic_args.as_slice() else {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "saturating intrinsic `{}` must have exactly one type argument",
                name.data(db),
            ))));
        };
        let suffix = integral_ty_suffix(db, *ty, "saturating helper")?;
        Ok(Some(format!("{prefix}_{suffix}")))
    }

    fn rewrite_numeric_calls<'db>(
        db: &'db DriverDataBase,
        module: &mut mir::MirModule<'db>,
    ) -> Result<FxHashSet<String>, EmitModuleError> {
        let mut required_helpers = FxHashSet::default();
        for func in &mut module.functions {
            for block in &mut func.body.blocks {
                for inst in &mut block.insts {
                    if let MirInst::Assign {
                        rvalue: Rvalue::Call(call),
                        ..
                    } = inst
                    {
                        let helper = if let Some(intrinsic) = call.checked_intrinsic {
                            Some(helper_symbol_from_checked_intrinsic(db, intrinsic)?)
                        } else {
                            helper_symbol_from_saturating_intrinsic(db, call)?
                        };
                        if let Some(helper) = helper {
                            required_helpers.insert(helper.clone());
                            call.resolved_name = Some(helper);
                        }
                    }
                }

                if let mir::Terminator::TerminatingCall {
                    call: mir::TerminatingCall::Call(call),
                    ..
                } = &mut block.terminator
                {
                    let helper = if let Some(intrinsic) = call.checked_intrinsic {
                        Some(helper_symbol_from_checked_intrinsic(db, intrinsic)?)
                    } else {
                        helper_symbol_from_saturating_intrinsic(db, call)?
                    };
                    if let Some(helper) = helper {
                        required_helpers.insert(helper.clone());
                        call.resolved_name = Some(helper);
                    }
                }
            }
        }
        Ok(required_helpers)
    }

    fn rewrite_numeric_call_aliases<'db>(
        db: &'db DriverDataBase,
        module: &mut mir::MirModule<'db>,
        aliases: &FxHashMap<String, String>,
    ) -> Result<(), EmitModuleError> {
        let rewrite_call = |call: &mut mir::CallOrigin<'db>| -> Result<(), EmitModuleError> {
            let helper = if let Some(intrinsic) = call.checked_intrinsic {
                Some(helper_symbol_from_checked_intrinsic(db, intrinsic)?)
            } else {
                helper_symbol_from_saturating_intrinsic(db, call)?
            };
            if let Some(helper) = helper
                && let Some(alias) = aliases.get(&helper)
            {
                call.resolved_name = Some(alias.clone());
            }
            Ok(())
        };

        for func in &mut module.functions {
            for block in &mut func.body.blocks {
                for inst in &mut block.insts {
                    if let MirInst::Assign {
                        rvalue: Rvalue::Call(call),
                        ..
                    } = inst
                    {
                        rewrite_call(call)?;
                    }
                }

                if let mir::Terminator::TerminatingCall {
                    call: mir::TerminatingCall::Call(call),
                    ..
                } = &mut block.terminator
                {
                    rewrite_call(call)?;
                }
            }
        }

        Ok(())
    }

    fn rewrite_call_targets<'db>(
        functions: &mut [mir::MirFunction<'db>],
        aliases: &FxHashMap<String, String>,
    ) {
        for func in functions {
            for block in &mut func.body.blocks {
                for inst in &mut block.insts {
                    if let MirInst::Assign {
                        rvalue: Rvalue::Call(call),
                        ..
                    } = inst
                        && let Some(name) = &call.resolved_name
                        && let Some(alias) = aliases.get(name)
                        && alias != name
                    {
                        call.resolved_name = Some(alias.clone());
                    }
                }

                if let mir::Terminator::TerminatingCall {
                    call: mir::TerminatingCall::Call(call),
                    ..
                } = &mut block.terminator
                    && let Some(name) = &call.resolved_name
                    && let Some(alias) = aliases.get(name)
                    && alias != name
                {
                    call.resolved_name = Some(alias.clone());
                }
            }
        }
    }

    fn fresh_internal_symbol(symbol: &str, known: &mut FxHashSet<String>) -> String {
        let base = format!("__internal_{symbol}");
        let mut candidate = base.clone();
        let mut suffix = 0;
        while !known.insert(candidate.clone()) {
            suffix += 1;
            candidate = format!("{base}_{suffix}");
        }
        candidate
    }

    let required_helpers = rewrite_numeric_calls(db, module)?;
    if required_helpers.is_empty() {
        return Ok(());
    }

    let current_ingot = module.top_mod.ingot(db);
    let core_ingot = if current_ingot.kind(db) == IngotKind::Core {
        current_ingot
    } else {
        current_ingot
            .resolved_external_ingots(db)
            .iter()
            .find_map(|(name, ingot)| {
                if name.data(db) == "core" {
                    Some(*ingot)
                } else {
                    None
                }
            })
            .ok_or_else(|| {
                EmitModuleError::Yul(YulError::Unsupported(
                    "failed to resolve `core` ingot while linking checked arithmetic helpers"
                        .into(),
                ))
            })?
    };

    let num_yul_url = core_ingot.base(db).join("src/num_yul.fe").map_err(|_| {
        EmitModuleError::Yul(YulError::Unsupported(
            "failed to locate `core::num_yul` source while linking checked arithmetic helpers"
                .into(),
        ))
    })?;
    let num_yul_file = db.workspace().get(db, &num_yul_url).ok_or_else(|| {
        EmitModuleError::Yul(YulError::Unsupported(
            "missing `core::num_yul` source while linking checked arithmetic helpers".into(),
        ))
    })?;
    let num_yul_top_mod = db.top_mod(num_yul_file);

    let mut num_yul_module =
        lower_module(db, num_yul_top_mod).map_err(EmitModuleError::MirLower)?;
    rewrite_numeric_calls(db, &mut num_yul_module)?;
    let num_yul_call_graph = build_call_graph(&num_yul_module.functions);

    let mut required_symbols = FxHashSet::default();
    for helper in &required_helpers {
        required_symbols.extend(reachable_functions(&num_yul_call_graph, helper));
    }

    let mut by_symbol: FxHashMap<_, _> = num_yul_module
        .functions
        .into_iter()
        .map(|func| (func.symbol_name.clone(), func))
        .collect();

    let mut known = FxHashSet::default();
    let mut known_sources = FxHashMap::default();
    for func in &module.functions {
        known.insert(func.symbol_name.clone());
        known_sources.insert(func.symbol_name.clone(), func.symbol_source);
    }

    let mut helper_aliases = FxHashMap::default();
    let mut imported_helpers = Vec::new();
    let mut symbols: Vec<_> = required_symbols.into_iter().collect();
    symbols.sort();
    for symbol in symbols {
        if known_sources.get(&symbol) == Some(&SymbolSource::Internal) {
            helper_aliases.insert(symbol.clone(), symbol);
            continue;
        }
        let Some(mut func) = by_symbol.remove(&symbol) else {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "missing required numeric helper function `{symbol}`"
            ))));
        };
        let final_symbol = if known.contains(&symbol) {
            fresh_internal_symbol(&symbol, &mut known)
        } else {
            known.insert(symbol.clone());
            symbol.clone()
        };
        helper_aliases.insert(symbol, final_symbol.clone());
        func.symbol_name = final_symbol;
        imported_helpers.push(func);
    }
    rewrite_numeric_call_aliases(db, module, &helper_aliases)?;
    rewrite_call_targets(&mut imported_helpers, &helper_aliases);
    module.functions.extend(imported_helpers);

    Ok(())
}

struct FunctionDocInfo {
    docs: Vec<YulDoc>,
    /// Data regions collected during emission for Yul data sections.
    data_regions: Vec<YulDataRegion>,
}

struct TestInfo {
    hir_name: String,
    display_name: String,
    symbol_name: String,
    object_name: String,
    value_param_count: usize,
    effect_param_count: usize,
    expected_revert: Option<ExpectedRevert>,
    initial_balance: Option<BigUint>,
}

/// Dependency set required to emit a single test object.
struct TestDependencies {
    contracts: FxHashSet<String>,
    code_region_roots: Vec<String>,
}

/// Collects metadata for each `#[test]` function in the lowered module.
///
/// * `db` - HIR database used to read attributes and names.
/// * `functions` - Monomorphized MIR functions to scan.
///
/// Returns a list of test info entries with placeholder names filled in.
fn collect_test_infos(
    db: &dyn HirDb,
    functions: &[MirFunction<'_>],
    filter: Option<&str>,
) -> Result<Vec<TestInfo>, EmitModuleError> {
    let mut tests = functions
        .iter()
        .filter_map(|mir_func| {
            let MirFunctionOrigin::Hir(hir_func) = mir_func.origin else {
                return None;
            };
            let attrs = ItemKind::from(hir_func).attrs(db)?;
            let test_attr = attrs.get_attr(db, "test")?;
            let hir_name = hir_func
                .name(db)
                .to_opt()
                .map(|n| n.data(db).to_string())
                .unwrap_or_else(|| "<anonymous>".to_string());
            let expected_revert = match parse_expected_revert(db, &hir_name, test_attr) {
                Ok(expected_revert) => expected_revert,
                Err(err) => return Some(Err(EmitModuleError::Yul(YulError::Unsupported(err)))),
            };
            // Check for #[test(balance = N)]
            let initial_balance = match parse_test_balance_arg(db, &hir_name, test_attr) {
                Ok(balance) => balance,
                Err(err) => return Some(Err(err)),
            };
            let value_param_count = mir_func.runtime_param_count();
            let effect_param_count = mir_func.runtime_effect_param_count();
            Some(Ok(TestInfo {
                hir_name,
                display_name: String::new(),
                symbol_name: mir_func.symbol_name.clone(),
                object_name: String::new(),
                value_param_count,
                effect_param_count,
                expected_revert,
                initial_balance,
            }))
        })
        .collect::<Result<Vec<_>, _>>()?;

    assign_test_display_names(&mut tests);
    assign_test_object_names(&mut tests);
    tests.retain(|test| test_info_matches_filter(test, filter));
    Ok(tests)
}

/// Extracts the `balance` argument from `#[test(balance = N)]`, if present.
fn parse_test_balance_arg<'db>(
    db: &'db dyn HirDb,
    test_name: &str,
    test_attr: &hir::hir_def::attr::NormalAttr<'db>,
) -> Result<Option<BigUint>, EmitModuleError> {
    for arg in &test_attr.args {
        if arg.key_str(db) != Some("balance") {
            continue;
        }
        let Some(value) = arg.value.as_ref() else {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] expects an integer literal"
            ))));
        };
        let hir::hir_def::attr::AttrArgValue::Lit(hir::hir_def::LitKind::Int(int_id)) = value
        else {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] expects an integer literal"
            ))));
        };
        let balance = int_id.data(db).clone();
        if balance.to_bytes_be().len() > 32 {
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] must fit in u256"
            ))));
        };
        return Ok(Some(balance));
    }

    Ok(None)
}
/// Parses the expected revert behavior from a `#[test(...)]` attribute.
///
/// Supported forms:
/// - `#[test(should_revert)]` — any revert
/// - `#[test(should_revert, selector = 0x4e487b71)]` — revert with matching 4-byte selector
/// - `#[test(should_revert, panic = 0x11)]` — revert with Panic(uint256) and matching code
pub fn parse_expected_revert<'db>(
    db: &'db dyn HirDb,
    test_name: &str,
    test_attr: &hir::hir_def::attr::NormalAttr<'db>,
) -> Result<Option<ExpectedRevert>, String> {
    let should_revert = test_attr.has_arg(db, "should_revert");
    let has_panic = has_test_attr_key(db, test_attr, "panic");
    let has_selector = has_test_attr_key(db, test_attr, "selector");

    if !should_revert {
        if has_panic && has_selector {
            return Err(format!(
                "invalid #[test] function `{test_name}`: `panic = ...` and `selector = ...` require `should_revert`"
            ));
        }
        if has_panic {
            return Err(format!(
                "invalid #[test] function `{test_name}`: `panic = ...` requires `should_revert`"
            ));
        }
        if has_selector {
            return Err(format!(
                "invalid #[test] function `{test_name}`: `selector = ...` requires `should_revert`"
            ));
        }
        return Ok(None);
    }

    let panic = parse_test_attr_int_arg(db, test_name, test_attr, "panic", "u256", 32)?;
    let selector = parse_test_attr_int_arg(db, test_name, test_attr, "selector", "u32", 4)?;

    if panic.is_some() && selector.is_some() {
        return Err(format!(
            "invalid #[test] function `{test_name}`: #[test(should_revert)] cannot combine `panic = ...` and `selector = ...`"
        ));
    }

    if let Some(code) = panic {
        let panic_selector: [u8; 4] = [0x4e, 0x48, 0x7b, 0x71];
        let mut payload = Vec::with_capacity(36);
        payload.extend_from_slice(&panic_selector);
        // ABI-encode the uint256 code: pad to 32 bytes big-endian
        let code_bytes = code.to_bytes_be();
        let mut padded = [0u8; 32];
        let start = 32 - code_bytes.len();
        padded[start..].copy_from_slice(&code_bytes);
        payload.extend_from_slice(&padded);
        return Ok(Some(ExpectedRevert::PanicCode(payload)));
    }

    if let Some(sel) = selector {
        let bytes = sel.to_bytes_be();
        let mut selector = [0u8; 4];
        let start = 4 - bytes.len();
        selector[start..].copy_from_slice(&bytes);
        return Ok(Some(ExpectedRevert::Selector(selector)));
    }

    Ok(Some(ExpectedRevert::Any))
}

fn has_test_attr_key<'db>(
    db: &'db dyn HirDb,
    test_attr: &hir::hir_def::attr::NormalAttr<'db>,
    key: &str,
) -> bool {
    test_attr
        .args
        .iter()
        .any(|arg| arg.key_str(db) == Some(key))
}

fn parse_test_attr_int_arg<'db>(
    db: &'db dyn HirDb,
    test_name: &str,
    test_attr: &hir::hir_def::attr::NormalAttr<'db>,
    key: &str,
    type_name: &str,
    max_bytes: usize,
) -> Result<Option<BigUint>, String> {
    for arg in &test_attr.args {
        if arg.key_str(db) != Some(key) {
            continue;
        }

        let Some(value) = arg.value.as_ref() else {
            return Err(format!(
                "invalid #[test] function `{test_name}`: #[test(should_revert, {key} = ...)] expects an integer literal"
            ));
        };
        let hir::hir_def::attr::AttrArgValue::Lit(hir::hir_def::LitKind::Int(int_id)) = value
        else {
            return Err(format!(
                "invalid #[test] function `{test_name}`: #[test(should_revert, {key} = ...)] expects an integer literal"
            ));
        };

        let value = int_id.data(db).clone();
        if value.to_bytes_be().len() > max_bytes {
            return Err(format!(
                "invalid #[test] function `{test_name}`: #[test(should_revert, {key} = ...)] must fit in {type_name}"
            ));
        }
        return Ok(Some(value));
    }

    Ok(None)
}

fn test_info_matches_filter(test: &TestInfo, filter: Option<&str>) -> bool {
    let Some(pattern) = filter else {
        return true;
    };
    test.hir_name.contains(pattern)
        || test.symbol_name.contains(pattern)
        || test.display_name.contains(pattern)
}

/// Validates that a `#[test]` function conforms to runner constraints.
///
/// * `db` - Driver database used for name lookup.
/// * `mir_func` - MIR function to validate.
/// * `returns_value` - Whether the function has a non-unit return type.
///
/// Returns `Ok(())` when valid or an [`EmitModuleError`] describing the issue.
fn validate_test_function(
    db: &DriverDataBase,
    mir_func: &MirFunction<'_>,
    returns_value: bool,
) -> Result<(), EmitModuleError> {
    let MirFunctionOrigin::Hir(hir_func) = mir_func.origin else {
        return Err(EmitModuleError::Yul(YulError::Unsupported(
            "invalid #[test] function: synthetic MIR functions cannot be tests".into(),
        )));
    };

    let name = function_name(db, hir_func);
    if mir_func.contract_function.is_some() {
        return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
            "invalid #[test] function `{name}`: contract entrypoints cannot be tests"
        ))));
    }
    if !is_free_test_function(db, hir_func) {
        return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
            "invalid #[test] function `{name}`: tests must be free functions (not in contracts or impls)"
        ))));
    }
    if returns_value {
        return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
            "invalid #[test] function `{name}`: tests must not return a value"
        ))));
    }
    Ok(())
}

/// Returns true if a test function is free (not inside a contract/impl/trait).
///
/// * `db` - HIR database for scope queries.
/// * `func` - HIR function to inspect.
fn is_free_test_function(db: &dyn HirAnalysisDb, func: hir::hir_def::Func<'_>) -> bool {
    if func.is_associated_func(db) {
        return false;
    }
    let Some(scope) = func.scope().parent(db) else {
        return true;
    };
    match scope {
        hir::hir_def::scope_graph::ScopeId::Item(item) => !matches!(item, ItemKind::Contract(_)),
        _ => true,
    }
}

/// Assigns human-readable display names and disambiguates duplicates.
///
/// * `tests` - Mutable list of test info entries to update.
///
/// Returns nothing; updates `tests` in place.
fn assign_test_display_names(tests: &mut [TestInfo]) {
    let mut name_counts: FxHashMap<String, usize> = FxHashMap::default();
    for test in tests.iter() {
        *name_counts.entry(test.hir_name.clone()).or_insert(0) += 1;
    }
    for test in tests.iter_mut() {
        let count = name_counts.get(&test.hir_name).copied().unwrap_or(0);
        if count > 1 {
            test.display_name = format!("{} [{}]", test.hir_name, test.symbol_name);
        } else {
            test.display_name = test.hir_name.clone();
        }
    }
}

/// Assigns unique Yul object names for each test, suffixing collisions.
///
/// * `tests` - Mutable list of test info entries to update.
///
/// Returns nothing; updates `tests` in place.
fn assign_test_object_names(tests: &mut [TestInfo]) {
    let mut groups: FxHashMap<String, Vec<usize>> = FxHashMap::default();
    for (idx, test) in tests.iter().enumerate() {
        let base = format!("test_{}", sanitize_symbol(&test.display_name));
        groups.entry(base).or_default().push(idx);
    }
    for (base, mut indices) in groups {
        if indices.len() == 1 {
            let idx = indices[0];
            tests[idx].object_name = base;
            continue;
        }
        indices.sort_by(|a, b| tests[*a].display_name.cmp(&tests[*b].display_name));
        for (suffix, idx) in indices.into_iter().enumerate() {
            tests[idx].object_name = format!("{base}_{}", suffix + 1);
        }
    }
}

/// Builds a lookup table from symbol name to MIR function.
///
/// * `functions` - Monomorphized MIR functions to index.
///
/// Returns a map keyed by symbol name.
fn build_funcs_by_symbol<'a>(
    functions: &'a [MirFunction<'a>],
) -> FxHashMap<String, &'a MirFunction<'a>> {
    functions
        .iter()
        .map(|func| (func.symbol_name.clone(), func))
        .collect()
}

/// Collects contracts and code-region roots needed to emit a single test object.
///
/// * `funcs_by_symbol` - Lookup from symbol name to MIR function.
/// * `call_graph` - Module call graph for reachability.
/// * `contract_graph` - Contract region dependency graph.
/// * `test_symbol` - Symbol name for the test entrypoint.
/// * `test_symbols` - Set of all test symbols (used to avoid recursion).
///
/// Returns the dependency set required by the test.
fn collect_test_dependencies(
    funcs_by_symbol: &FxHashMap<String, &MirFunction<'_>>,
    call_graph: &CallGraph,
    contract_graph: &mir::analysis::ContractGraph,
    test_symbol: &str,
    test_symbols: &FxHashSet<String>,
) -> TestDependencies {
    let mut contract_regions = FxHashSet::default();
    let mut code_region_roots = FxHashSet::default();
    let mut queue = VecDeque::new();

    let reachable = reachable_functions(call_graph, test_symbol);
    for symbol in &reachable {
        if let Some(region) = contract_graph.symbol_to_region.get(symbol) {
            contract_regions.insert(region.clone());
        }
        let Some(func) = funcs_by_symbol.get(symbol) else {
            continue;
        };
        collect_code_region_targets(
            func,
            contract_graph,
            test_symbols,
            &mut queue,
            &mut contract_regions,
        );
    }

    while let Some(root) = queue.pop_front() {
        if contract_graph.symbol_to_region.contains_key(&root) {
            if let Some(region) = contract_graph.symbol_to_region.get(&root) {
                contract_regions.insert(region.clone());
            }
            continue;
        }
        if test_symbols.contains(&root) {
            continue;
        }
        if !code_region_roots.insert(root.clone()) {
            continue;
        }
        let reachable_root = reachable_functions(call_graph, &root);
        for symbol in &reachable_root {
            if let Some(region) = contract_graph.symbol_to_region.get(symbol) {
                contract_regions.insert(region.clone());
            }
            let Some(func) = funcs_by_symbol.get(symbol) else {
                continue;
            };
            collect_code_region_targets(
                func,
                contract_graph,
                test_symbols,
                &mut queue,
                &mut contract_regions,
            );
        }
    }

    let mut region_queue: VecDeque<_> = contract_regions.iter().cloned().collect();
    while let Some(region) = region_queue.pop_front() {
        let Some(deps) = contract_graph.region_deps.get(&region) else {
            continue;
        };
        for dep in deps {
            if contract_regions.insert(dep.clone()) {
                region_queue.push_back(dep.clone());
            }
        }
    }

    let mut contracts = FxHashSet::default();
    for region in contract_regions {
        contracts.insert(region.contract_name);
    }

    let mut code_region_roots: Vec<_> = code_region_roots.into_iter().collect();
    code_region_roots.sort();

    TestDependencies {
        contracts,
        code_region_roots,
    }
}

/// Scans a function for `code_region_offset/len` intrinsics and queues targets.
///
/// * `func` - MIR function to scan.
/// * `contract_graph` - Contract region lookup for code region symbols.
/// * `test_symbols` - Set of test symbols to skip as code region roots.
/// * `queue` - Worklist of code region roots to process.
/// * `contract_regions` - Output set of referenced contract regions.
///
/// Returns nothing; updates `queue` and `contract_regions`.
fn collect_code_region_targets(
    func: &MirFunction<'_>,
    contract_graph: &mir::analysis::ContractGraph,
    test_symbols: &FxHashSet<String>,
    queue: &mut VecDeque<String>,
    contract_regions: &mut FxHashSet<ContractRegion>,
) {
    for block in &func.body.blocks {
        for inst in &block.insts {
            let MirInst::Assign {
                rvalue:
                    Rvalue::Intrinsic {
                        op: IntrinsicOp::CodeRegionLen | IntrinsicOp::CodeRegionOffset,
                        args,
                    },
                ..
            } = inst
            else {
                continue;
            };
            let Some(arg) = args.first().copied() else {
                continue;
            };
            let ValueOrigin::CodeRegionRef(target) = &func.body.value(arg).origin else {
                continue;
            };
            let Some(target_symbol) = &target.symbol else {
                continue;
            };
            if let Some(region) = contract_graph.symbol_to_region.get(target_symbol) {
                contract_regions.insert(region.clone());
            } else if !test_symbols.contains(target_symbol) {
                queue.push_back(target_symbol.clone());
            }
        }
    }
}

/// Emits Yul docs for the included contract init/deployed objects.
///
/// * `contract_graph` - Contract region dependency graph.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `included_contracts` - Contract names to include in the output.
///
/// Returns Yul docs for the root contract objects or an [`EmitModuleError`].
fn emit_contract_docs(
    contract_graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    included_contracts: &FxHashSet<String>,
) -> Result<Vec<YulDoc>, EmitModuleError> {
    if included_contracts.is_empty() {
        return Ok(Vec::new());
    }
    let mut contract_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut referenced_contracts = FxHashSet::default();
    for (from_region, deps) in &contract_graph.region_deps {
        if !included_contracts.contains(&from_region.contract_name) {
            continue;
        }
        for dep in deps {
            if dep.contract_name != from_region.contract_name
                && included_contracts.contains(&dep.contract_name)
            {
                referenced_contracts.insert(dep.contract_name.clone());
                contract_deps
                    .entry(from_region.contract_name.clone())
                    .or_default()
                    .insert(dep.contract_name.clone());
            }
        }
    }

    let mut root_contracts: Vec<_> = included_contracts
        .iter()
        .filter(|name| !referenced_contracts.contains(*name))
        .cloned()
        .collect();
    root_contracts.sort();

    if !included_contracts.is_empty() {
        let mut visited = FxHashSet::default();
        let mut queue = VecDeque::new();
        for name in &root_contracts {
            queue.push_back(name.clone());
        }
        while let Some(name) = queue.pop_front() {
            if !visited.insert(name.clone()) {
                continue;
            }
            if let Some(deps) = contract_deps.get(&name) {
                for dep in deps {
                    queue.push_back(dep.clone());
                }
            }
        }
        if visited.len() != included_contracts.len() {
            let mut missing: Vec<_> = contract_graph
                .contracts
                .keys()
                .filter(|name| included_contracts.contains(*name))
                .filter(|name| !visited.contains(*name))
                .cloned()
                .collect();
            missing.sort();
            return Err(EmitModuleError::Yul(YulError::Unsupported(format!(
                "contract region graph is not rooted (cycle likely); unreachable contracts: {}",
                missing.join(", ")
            ))));
        }
    }

    let mut docs = Vec::new();
    for name in root_contracts {
        if !contract_graph.contracts.contains_key(&name) {
            continue;
        }
        let mut stack = Vec::new();
        docs.push(
            emit_contract_init_object(&name, contract_graph, docs_by_symbol, &mut stack)
                .map_err(EmitModuleError::Yul)?,
        );
    }
    Ok(docs)
}

/// Emits Yul docs for standalone code regions reachable from the provided roots.
///
/// * `call_graph` - Module call graph for reachability.
/// * `code_region_roots` - Root symbols to emit as code-region objects.
/// * `contract_graph` - Contract region graph used to skip contract entrypoints.
/// * `code_regions` - Mapping from symbol name to object label.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `skip_roots` - Symbols to omit (e.g., test entrypoints).
///
/// Returns the Yul docs for each emitted code-region object.
fn emit_code_region_docs(
    call_graph: &CallGraph,
    code_region_roots: &[String],
    contract_graph: &mir::analysis::ContractGraph,
    code_regions: &FxHashMap<String, String>,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    skip_roots: &FxHashSet<String>,
) -> Vec<YulDoc> {
    let mut docs = Vec::new();
    for root in code_region_roots {
        if skip_roots.contains(root) {
            continue;
        }
        if contract_graph.symbol_to_region.contains_key(root) {
            continue;
        }
        let Some(label) = code_regions.get(root) else {
            continue;
        };
        let reachable = reachable_functions(call_graph, root);
        let mut region_docs = Vec::new();
        let mut seen_labels = FxHashSet::default();
        let mut data_regions = Vec::new();
        let mut symbols: Vec<_> = reachable.into_iter().collect();
        symbols.sort();
        for symbol in symbols {
            if let Some(info) = docs_by_symbol.get(&symbol) {
                region_docs.extend(info.docs.clone());
                for dr in &info.data_regions {
                    if seen_labels.insert(dr.label.clone()) {
                        data_regions.push(dr.clone());
                    }
                }
            }
        }
        let mut components = vec![YulDoc::block("code ", region_docs)];
        components.extend(emit_data_sections(&data_regions));
        docs.push(YulDoc::block(format!("object \"{label}\" "), components));
    }
    docs
}

/// Emits a runnable Yul object for a single test, including dependencies.
///
/// * `call_graph` - Module call graph for reachability.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `dependency_docs` - Yul docs for contract/code-region dependencies.
/// * `test` - Test metadata describing the entrypoint and arity.
///
/// Returns the assembled Yul doc tree for the test object.
fn emit_test_object(
    call_graph: &CallGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    dependency_docs: &[YulDoc],
    test: &TestInfo,
) -> Result<YulDoc, EmitModuleError> {
    let reachable = reachable_functions(call_graph, &test.symbol_name);
    let mut symbols: Vec<_> = reachable.into_iter().collect();
    symbols.sort();

    let mut runtime_docs = Vec::new();
    let mut data_regions = Vec::new();
    let mut seen_labels = FxHashSet::default();
    for symbol in symbols {
        if let Some(info) = docs_by_symbol.get(&symbol) {
            runtime_docs.extend(info.docs.clone());
            // Collect data regions from reachable functions
            for dr in &info.data_regions {
                if seen_labels.insert(dr.label.clone()) {
                    data_regions.push(dr.clone());
                }
            }
        }
    }

    let total_param_count = test.value_param_count + test.effect_param_count;
    let call_args = format_call_args(total_param_count);
    let test_symbol = prefix_yul_name(&test.symbol_name);
    if call_args.is_empty() {
        runtime_docs.push(YulDoc::line(format!("{test_symbol}()")));
    } else {
        runtime_docs.push(YulDoc::line(format!("{test_symbol}({call_args})")));
    }
    runtime_docs.push(YulDoc::line("return(0, 0)"));

    let mut runtime_components = vec![YulDoc::block("code ", runtime_docs)];
    for doc in dependency_docs {
        runtime_components.push(YulDoc::line(String::new()));
        runtime_components.push(doc.clone());
    }

    // Emit data sections in the runtime object
    runtime_components.extend(emit_data_sections(&data_regions));

    let runtime_obj = YulDoc::block("object \"runtime\" ", runtime_components);

    let mut components = vec![YulDoc::block(
        "code ",
        vec![
            YulDoc::line("datacopy(0, dataoffset(\"runtime\"), datasize(\"runtime\"))"),
            YulDoc::line("return(0, datasize(\"runtime\"))"),
        ],
    )];
    components.push(YulDoc::line(String::new()));
    components.push(runtime_obj);

    Ok(YulDoc::block(
        format!("object \"{}\" ", test.object_name),
        components,
    ))
}

/// Formats a comma-separated list of zero literals for the given arity.
///
/// * `count` - Number of arguments to generate.
///
/// Returns the argument list string or an empty string when `count` is zero.
fn format_call_args(count: usize) -> String {
    if count == 0 {
        return String::new();
    }
    std::iter::repeat_n("0", count)
        .collect::<Vec<_>>()
        .join(", ")
}

/// Emits the contract init object and its direct region dependencies.
///
/// * `name` - Contract name to emit.
/// * `graph` - Contract region dependency graph.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `stack` - Region stack used for cycle detection.
///
/// Returns the Yul doc for the init object or a [`YulError`].
fn emit_contract_init_object(
    name: &str,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    let entry = graph
        .contracts
        .get(name)
        .ok_or_else(|| YulError::Unsupported(format!("missing contract info for `{name}`")))?;
    let region = ContractRegion {
        contract_name: name.to_string(),
        kind: ContractRegionKind::Init,
    };
    push_region(stack, &region)?;

    let mut components = Vec::new();

    let mut init_docs = Vec::new();
    if let Some(symbol) = &entry.init_symbol {
        init_docs.extend(reachable_docs_for_region(graph, &region, docs_by_symbol));
        let symbol = prefix_yul_name(symbol);
        init_docs.push(YulDoc::line(format!("{symbol}()")));
    }
    components.push(YulDoc::block("code ", init_docs));

    // Always emit the deployed object (if present) for the contract itself.
    if entry.deployed_symbol.is_some() {
        components.push(YulDoc::line(String::new()));
        components.push(emit_contract_deployed_object(
            name,
            graph,
            docs_by_symbol,
            stack,
        )?);
    }

    // Emit direct region dependencies as children of the init object. These must be direct
    // children to satisfy Yul `dataoffset/datasize` scoping rules.
    let deps = graph.region_deps.get(&region).cloned().unwrap_or_default();
    let mut deps: Vec<_> = deps
        .into_iter()
        .filter(|dep| {
            !(dep.contract_name == name && matches!(dep.kind, ContractRegionKind::Deployed))
        })
        .collect();
    deps.sort();
    for dep in deps {
        components.push(emit_region_object(&dep, graph, docs_by_symbol, stack)?);
    }

    // Emit data sections for this region (large const strings/arrays)
    let data_regions = reachable_data_regions_for_region(graph, &region, docs_by_symbol);
    components.extend(emit_data_sections(&data_regions));

    pop_region(stack, &region);
    Ok(YulDoc::block(format!("object \"{name}\" "), components))
}

/// Emits the deployed/runtime object for a contract.
///
/// * `contract_name` - Contract name to emit.
/// * `graph` - Contract region dependency graph.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `stack` - Region stack used for cycle detection.
///
/// Returns the Yul doc for the deployed object or a [`YulError`].
fn emit_contract_deployed_object(
    contract_name: &str,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    let entry = graph.contracts.get(contract_name).ok_or_else(|| {
        YulError::Unsupported(format!("missing contract info for `{contract_name}`"))
    })?;
    let Some(symbol) = &entry.deployed_symbol else {
        return Err(YulError::Unsupported(format!(
            "missing deployed entrypoint for `{contract_name}`"
        )));
    };

    let region = ContractRegion {
        contract_name: contract_name.to_string(),
        kind: ContractRegionKind::Deployed,
    };
    push_region(stack, &region)?;

    let mut runtime_docs = Vec::new();
    runtime_docs.extend(reachable_docs_for_region(graph, &region, docs_by_symbol));
    let symbol = prefix_yul_name(symbol);
    runtime_docs.push(YulDoc::line(format!("{symbol}()")));
    runtime_docs.push(YulDoc::line("return(0, 0)"));

    let mut components = vec![YulDoc::block("code ", runtime_docs)];

    let deps = graph.region_deps.get(&region).cloned().unwrap_or_default();
    let mut deps: Vec<_> = deps.into_iter().collect();
    deps.sort();
    for dep in deps {
        components.push(emit_region_object(&dep, graph, docs_by_symbol, stack)?);
    }

    // Emit data sections for this region (large const strings/arrays)
    let data_regions = reachable_data_regions_for_region(graph, &region, docs_by_symbol);
    components.extend(emit_data_sections(&data_regions));

    pop_region(stack, &region);
    Ok(YulDoc::block(
        format!("object \"{contract_name}_deployed\" "),
        components,
    ))
}

/// Dispatches region emission based on the region kind.
///
/// * `region` - Target contract region.
/// * `graph` - Contract region dependency graph.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
/// * `stack` - Region stack used for cycle detection.
///
/// Returns the Yul doc for the requested region.
fn emit_region_object(
    region: &ContractRegion,
    graph: &mir::analysis::ContractGraph,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
    stack: &mut Vec<ContractRegion>,
) -> Result<YulDoc, YulError> {
    match region.kind {
        ContractRegionKind::Init => {
            emit_contract_init_object(&region.contract_name, graph, docs_by_symbol, stack)
        }
        ContractRegionKind::Deployed => {
            emit_contract_deployed_object(&region.contract_name, graph, docs_by_symbol, stack)
        }
    }
}

/// Collects emitted Yul docs for symbols reachable from a contract region.
///
/// * `graph` - Contract region dependency graph.
/// * `region` - Region whose reachable symbols should be emitted.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs.
///
/// Returns the Yul docs in stable symbol order.
fn reachable_docs_for_region(
    graph: &mir::analysis::ContractGraph,
    region: &ContractRegion,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
) -> Vec<YulDoc> {
    let mut docs = Vec::new();
    let Some(reachable) = graph.region_reachable.get(region) else {
        return docs;
    };
    let mut symbols: Vec<_> = reachable.iter().cloned().collect();
    symbols.sort();
    for symbol in symbols {
        if let Some(info) = docs_by_symbol.get(&symbol) {
            docs.extend(info.docs.clone());
        }
    }
    docs
}

/// Pushes a region onto the stack, reporting cycles as errors.
///
/// * `stack` - Active region stack used for cycle detection.
/// * `region` - Region to push onto the stack.
///
/// Returns `Ok(())` or a [`YulError`] when a cycle is detected.
fn push_region(stack: &mut Vec<ContractRegion>, region: &ContractRegion) -> Result<(), YulError> {
    if stack.iter().any(|r| r == region) {
        let mut cycle = stack
            .iter()
            .map(|r| format!("{}::{:?}", r.contract_name, r.kind))
            .collect::<Vec<_>>();
        cycle.push(format!("{}::{:?}", region.contract_name, region.kind));
        return Err(YulError::Unsupported(format!(
            "cycle detected in contract region graph: {}",
            cycle.join(" -> ")
        )));
    }
    stack.push(region.clone());
    Ok(())
}

/// Pops the last region and asserts it matches `region`.
///
/// * `stack` - Active region stack.
/// * `region` - Region expected at the top of the stack.
///
/// Returns nothing.
fn pop_region(stack: &mut Vec<ContractRegion>, region: &ContractRegion) {
    let popped = stack.pop();
    debug_assert_eq!(popped.as_ref(), Some(region));
}

/// Collects data regions for symbols reachable from a contract region.
///
/// * `graph` - Contract region dependency graph.
/// * `region` - Region whose data regions should be collected.
/// * `docs_by_symbol` - Map from function symbol to emitted Yul docs and data regions.
///
/// Returns the data regions in stable symbol order, deduplicated by label.
fn reachable_data_regions_for_region(
    graph: &mir::analysis::ContractGraph,
    region: &ContractRegion,
    docs_by_symbol: &FxHashMap<String, FunctionDocInfo>,
) -> Vec<YulDataRegion> {
    let mut data_regions = Vec::new();
    let mut seen_labels = FxHashSet::default();
    let Some(reachable) = graph.region_reachable.get(region) else {
        return data_regions;
    };
    let mut symbols: Vec<_> = reachable.iter().cloned().collect();
    symbols.sort();
    for symbol in symbols {
        if let Some(info) = docs_by_symbol.get(&symbol) {
            for dr in &info.data_regions {
                if seen_labels.insert(dr.label.clone()) {
                    data_regions.push(dr.clone());
                }
            }
        }
    }
    data_regions
}

/// Emits Yul data sections for a list of data region definitions.
///
/// * `data_regions` - Data regions to emit.
///
/// Returns Yul docs for each data section.
fn emit_data_sections(data_regions: &[YulDataRegion]) -> Vec<YulDoc> {
    data_regions
        .iter()
        .map(|dr| {
            YulDoc::line(format!(
                "data \"{}\" hex\"{}\"",
                dr.label,
                hex::encode(&dr.bytes)
            ))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{TestInfo, assign_test_object_names, test_info_matches_filter};

    /// Ensures test object names are disambiguated with numeric suffixes.
    #[test]
    fn test_object_name_collision_suffixes() {
        let mut tests = vec![
            TestInfo {
                hir_name: "foo".to_string(),
                display_name: "foo bar".to_string(),
                symbol_name: "sym1".to_string(),
                object_name: String::new(),
                value_param_count: 0,
                effect_param_count: 0,
                expected_revert: None,
                initial_balance: None,
            },
            TestInfo {
                hir_name: "foo_bar".to_string(),
                display_name: "foo_bar".to_string(),
                symbol_name: "sym2".to_string(),
                object_name: String::new(),
                value_param_count: 0,
                effect_param_count: 0,
                expected_revert: None,
                initial_balance: None,
            },
        ];

        assign_test_object_names(&mut tests);

        let mut by_name = tests
            .into_iter()
            .map(|test| (test.display_name, test.object_name))
            .collect::<std::collections::HashMap<_, _>>();

        assert_eq!(by_name.remove("foo bar").as_deref(), Some("test_foo_bar_1"));
        assert_eq!(by_name.remove("foo_bar").as_deref(), Some("test_foo_bar_2"));
    }

    #[test]
    fn test_filter_matches_hir_symbol_and_display_names() {
        let test = TestInfo {
            hir_name: "alpha".to_string(),
            display_name: "alpha [module::alpha]".to_string(),
            symbol_name: "module_h123_alpha".to_string(),
            object_name: "test_alpha".to_string(),
            value_param_count: 0,
            effect_param_count: 0,
            expected_revert: None,
            initial_balance: None,
        };

        assert!(test_info_matches_filter(&test, None));
        assert!(test_info_matches_filter(&test, Some("alpha")));
        assert!(test_info_matches_filter(&test, Some("module_h123")));
        assert!(!test_info_matches_filter(&test, Some("beta")));
    }
}
