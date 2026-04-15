use driver::DriverDataBase;
use hir::HirDb;
use hir::hir_def::{ItemKind, TopLevelMod};
use mir::analysis::{CallGraph, build_call_graph, reachable_functions};
use mir::{
    MirFunction, MirInst, Rvalue,
    ir::{IntrinsicOp, MirFunctionOrigin},
    layout, lower_ingot,
};
use num_bigint::BigUint;
use rustc_hash::{FxHashMap, FxHashSet};
use sonatina_codegen::{
    isa::evm::EvmBackend,
    object::{CompileOptions, ObjectArtifact, compile_all_objects},
};
use sonatina_ir::{
    Module, Signature,
    builder::ModuleBuilder,
    func_cursor::InstInserter,
    inst::{control_flow::Call, evm::EvmStop},
    isa::Isa,
    module::ModuleCtx,
    object::{Directive, Embed, EmbedSymbol, Object, ObjectName, Section, SectionName, SectionRef},
};
use sonatina_verifier::{VerificationLevel, VerifierConfig};

use crate::{ExpectedRevert, OptLevel, TestMetadata, TestModuleOutput, parse_expected_revert};

use super::{ContractObjectSelection, LowerError, ModuleLowerer};

#[derive(Debug, Clone, Copy, Default)]
pub struct SonatinaTestOptions {
    pub emit_observability: bool,
}

pub fn emit_test_module_sonatina(
    db: &DriverDataBase,
    top_mod: TopLevelMod<'_>,
    opt_level: OptLevel,
    options: SonatinaTestOptions,
    filter: Option<&str>,
) -> Result<TestModuleOutput, LowerError> {
    let ingot = top_mod.ingot(db);
    let mir_module = lower_ingot(db, ingot)?;

    let tests = collect_tests(db, &mir_module.functions, filter)?;
    if tests.is_empty() {
        return Ok(TestModuleOutput { tests: Vec::new() });
    }

    let call_graph = build_call_graph(&mir_module.functions);
    let funcs_by_symbol = build_funcs_by_symbol(&mir_module.functions);

    let code_region_roots = collect_code_region_roots(&mir_module.functions);
    let code_region_sections = code_region_roots
        .iter()
        .map(|sym| (sym.clone(), code_region_section_name(sym)))
        .collect::<FxHashMap<_, _>>();

    // Validate roots exist in the lowered module.
    for root in &code_region_roots {
        if !funcs_by_symbol.contains_key(root.as_str()) {
            return Err(LowerError::Internal(format!(
                "code region root `{root}` has no MIR function"
            )));
        }
    }

    // Precompute region reachability + region deps (for nested embeds).
    let mut region_reachable: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    let mut region_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
    for root in &code_region_roots {
        let reachable = reachable_functions(&call_graph, root);
        let deps = collect_code_region_deps(&reachable, &funcs_by_symbol);
        region_reachable.insert(root.clone(), reachable);
        region_deps.insert(root.clone(), deps);
    }
    let (needed_symbols, needed_code_regions) = collect_needed_symbols_for_tests(
        &tests,
        &call_graph,
        &funcs_by_symbol,
        &region_reachable,
        &region_deps,
    )?;
    detect_code_region_cycles(&filter_code_region_graph(
        &needed_code_regions,
        &region_deps,
    ))?;

    let mut module = compile_test_objects(
        db,
        &mir_module,
        &tests,
        &needed_symbols,
        &needed_code_regions,
        &call_graph,
        &funcs_by_symbol,
        &code_region_sections,
        &region_deps,
    )?;
    super::ensure_module_sonatina_ir_valid(&module)?;
    run_sonatina_optimization_pipeline(&mut module, opt_level);
    super::ensure_module_sonatina_ir_valid(&module)?;

    // Compile all objects at once to avoid repeated prepare_section mutations
    // on shared functions. compile_all_objects builds a single section cache
    // so each function is lowered exactly once.
    let all_artifacts = compile_all_objects_for_tests(&module, options)?;

    let mut output_tests = Vec::with_capacity(tests.len());
    for test in tests {
        let runtime = extract_runtime_from_artifact(&all_artifacts, &test.object_name)?;
        let init_bytecode = wrap_as_init_code(&runtime.bytes);

        output_tests.push(TestMetadata {
            display_name: test.display_name,
            hir_name: test.hir_name,
            symbol_name: test.symbol_name,
            object_name: test.object_name,
            yul: String::new(),
            bytecode: init_bytecode,
            sonatina_observability_json: runtime.observability_json,
            value_param_count: test.value_param_count,
            effect_param_count: test.effect_param_count,
            expected_revert: test.expected_revert.clone(),
            initial_balance: test.initial_balance.map(|b| b.to_bytes_be()),
        });
    }

    Ok(TestModuleOutput {
        tests: output_tests,
    })
}

fn run_sonatina_optimization_pipeline(module: &mut Module, opt_level: OptLevel) {
    match opt_level {
        OptLevel::O0 => { /* no optimization */ }
        OptLevel::Os => sonatina_codegen::optim::Pipeline::size().run(module),
        OptLevel::O2 => sonatina_codegen::optim::Pipeline::speed().run(module),
    }
}

#[derive(Debug, Clone)]
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

fn collect_tests(
    db: &DriverDataBase,
    functions: &[MirFunction<'_>],
    filter: Option<&str>,
) -> Result<Vec<TestInfo>, LowerError> {
    let mut tests: Vec<TestInfo> = functions
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
                Err(err) => return Some(Err(LowerError::Unsupported(err))),
            };
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
) -> Result<Option<BigUint>, LowerError> {
    for arg in &test_attr.args {
        if arg.key_str(db) != Some("balance") {
            continue;
        }
        let Some(value) = arg.value.as_ref() else {
            return Err(LowerError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] expects an integer literal"
            )));
        };
        let hir::hir_def::attr::AttrArgValue::Lit(hir::hir_def::LitKind::Int(int_id)) = value
        else {
            return Err(LowerError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] expects an integer literal"
            )));
        };
        let balance = int_id.data(db).clone();
        if balance.to_bytes_be().len() > 32 {
            return Err(LowerError::Unsupported(format!(
                "invalid #[test] function `{test_name}`: #[test(balance = ...)] must fit in u256"
            )));
        };
        return Ok(Some(balance));
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

fn sanitize_symbol(component: &str) -> String {
    component
        .chars()
        .map(|ch| if ch.is_ascii_alphanumeric() { ch } else { '_' })
        .collect()
}

fn build_funcs_by_symbol<'a>(
    functions: &'a [MirFunction<'a>],
) -> FxHashMap<&'a str, &'a MirFunction<'a>> {
    functions
        .iter()
        .map(|func| (func.symbol_name.as_str(), func))
        .collect()
}

fn collect_code_region_roots(functions: &[MirFunction<'_>]) -> Vec<String> {
    let mut roots = FxHashSet::default();
    for func in functions {
        if func.contract_function.is_some() {
            roots.insert(func.symbol_name.clone());
        }
        for block in &func.body.blocks {
            for inst in &block.insts {
                let MirInst::Assign {
                    rvalue:
                        Rvalue::Intrinsic {
                            op: IntrinsicOp::CodeRegionOffset | IntrinsicOp::CodeRegionLen,
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
                let mir::ValueOrigin::CodeRegionRef(target) = &func.body.value(arg).origin else {
                    continue;
                };
                let Some(symbol) = &target.symbol else {
                    continue;
                };
                roots.insert(symbol.clone());
            }
        }
    }
    let mut out: Vec<_> = roots.into_iter().collect();
    out.sort();
    out
}

fn collect_code_region_deps(
    reachable: &FxHashSet<String>,
    funcs_by_symbol: &FxHashMap<&str, &MirFunction<'_>>,
) -> FxHashSet<String> {
    let mut deps = FxHashSet::default();
    for symbol in reachable {
        let Some(func) = funcs_by_symbol.get(symbol.as_str()).copied() else {
            continue;
        };
        for block in &func.body.blocks {
            for inst in &block.insts {
                let MirInst::Assign {
                    rvalue:
                        Rvalue::Intrinsic {
                            op: IntrinsicOp::CodeRegionOffset | IntrinsicOp::CodeRegionLen,
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
                let mir::ValueOrigin::CodeRegionRef(target) = &func.body.value(arg).origin else {
                    continue;
                };
                let Some(target_symbol) = &target.symbol else {
                    continue;
                };
                deps.insert(target_symbol.clone());
            }
        }
    }
    deps
}

fn detect_code_region_cycles(
    graph: &FxHashMap<String, FxHashSet<String>>,
) -> Result<(), LowerError> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Mark {
        Visiting,
        Visited,
    }

    fn dfs(
        node: &str,
        graph: &FxHashMap<String, FxHashSet<String>>,
        marks: &mut FxHashMap<String, Mark>,
        stack: &mut Vec<String>,
    ) -> Result<(), LowerError> {
        match marks.get(node).copied() {
            Some(Mark::Visited) => return Ok(()),
            Some(Mark::Visiting) => {
                let start = stack.iter().position(|n| n == node).unwrap_or(0);
                let mut cycle = stack[start..].to_vec();
                cycle.push(node.to_string());
                return Err(LowerError::Unsupported(format!(
                    "cycle detected in code region graph: {}",
                    cycle.join(" -> ")
                )));
            }
            None => {}
        }

        marks.insert(node.to_string(), Mark::Visiting);
        stack.push(node.to_string());
        if let Some(deps) = graph.get(node) {
            let mut deps: Vec<String> = deps.iter().cloned().collect();
            deps.sort();
            for dep in deps {
                if dep == node {
                    continue;
                }
                dfs(&dep, graph, marks, stack)?;
            }
        }
        stack.pop();
        marks.insert(node.to_string(), Mark::Visited);
        Ok(())
    }

    let mut marks = FxHashMap::default();
    let mut stack = Vec::new();
    let mut nodes: Vec<String> = graph.keys().cloned().collect();
    nodes.sort();
    for node in nodes {
        dfs(&node, graph, &mut marks, &mut stack)?;
    }
    Ok(())
}

fn collect_needed_symbols_for_tests(
    tests: &[TestInfo],
    call_graph: &CallGraph,
    funcs_by_symbol: &FxHashMap<&str, &MirFunction<'_>>,
    region_reachable: &FxHashMap<String, FxHashSet<String>>,
    region_deps: &FxHashMap<String, FxHashSet<String>>,
) -> Result<(FxHashSet<String>, Vec<String>), LowerError> {
    fn include_code_region(
        root: &str,
        needed_symbols: &mut FxHashSet<String>,
        needed_code_regions: &mut FxHashSet<String>,
        region_reachable: &FxHashMap<String, FxHashSet<String>>,
        region_deps: &FxHashMap<String, FxHashSet<String>>,
    ) -> Result<(), LowerError> {
        if !needed_code_regions.insert(root.to_string()) {
            return Ok(());
        }
        let Some(region_symbols) = region_reachable.get(root) else {
            return Err(LowerError::Internal(format!(
                "test depends on unknown code region `{root}`"
            )));
        };
        needed_symbols.extend(region_symbols.iter().cloned());

        let mut deps = region_deps
            .get(root)
            .cloned()
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        deps.sort();
        for dep in deps {
            if dep != root {
                include_code_region(
                    &dep,
                    needed_symbols,
                    needed_code_regions,
                    region_reachable,
                    region_deps,
                )?;
            }
        }
        Ok(())
    }

    let mut needed_symbols = FxHashSet::default();
    let mut needed_code_regions = FxHashSet::default();

    for test in tests {
        let reachable = reachable_functions(call_graph, &test.symbol_name);
        needed_symbols.extend(reachable.iter().cloned());

        let mut deps = collect_code_region_deps(&reachable, funcs_by_symbol)
            .into_iter()
            .collect::<Vec<_>>();
        deps.sort();
        for dep in deps {
            include_code_region(
                &dep,
                &mut needed_symbols,
                &mut needed_code_regions,
                region_reachable,
                region_deps,
            )?;
        }
    }

    let mut needed_code_regions: Vec<String> = needed_code_regions.into_iter().collect();
    needed_code_regions.sort();
    Ok((needed_symbols, needed_code_regions))
}

fn filter_code_region_graph(
    needed_code_regions: &[String],
    region_deps: &FxHashMap<String, FxHashSet<String>>,
) -> FxHashMap<String, FxHashSet<String>> {
    let needed_set: FxHashSet<String> = needed_code_regions.iter().cloned().collect();
    needed_code_regions
        .iter()
        .map(|root| {
            let deps = region_deps
                .get(root)
                .into_iter()
                .flatten()
                .filter(|dep| needed_set.contains(*dep))
                .cloned()
                .collect();
            (root.clone(), deps)
        })
        .collect()
}

fn code_region_section_name(symbol: &str) -> SectionName {
    SectionName::from(format!("code_region_{}", sanitize_symbol(symbol)))
}

#[allow(clippy::too_many_arguments)]
fn compile_test_objects(
    db: &DriverDataBase,
    mir_module: &mir::MirModule<'_>,
    tests: &[TestInfo],
    needed_symbols: &FxHashSet<String>,
    needed_code_regions: &[String],
    call_graph: &CallGraph,
    funcs_by_symbol: &FxHashMap<&str, &MirFunction<'_>>,
    code_region_sections: &FxHashMap<String, SectionName>,
    region_deps: &FxHashMap<String, FxHashSet<String>>,
) -> Result<Module, LowerError> {
    let isa = super::create_evm_isa();
    let ctx = ModuleCtx::new(&isa);
    let builder = ModuleBuilder::new(ctx);

    let mut lowerer = ModuleLowerer::new(
        db,
        builder,
        mir_module,
        &isa,
        layout::EVM_LAYOUT,
        ContractObjectSelection::All,
    );
    lowerer.declare_functions_for_tests(needed_symbols)?;

    if !needed_code_regions.is_empty() {
        let code_regions_object = create_code_regions_object(
            &mut lowerer,
            funcs_by_symbol,
            needed_code_regions,
            code_region_sections,
            region_deps,
        )?;
        lowerer
            .builder
            .declare_object(code_regions_object)
            .map_err(|e| {
                LowerError::Internal(format!("failed to declare CodeRegions object: {e}"))
            })?;
    }

    for test in tests {
        let object = create_test_object(
            &mut lowerer,
            funcs_by_symbol,
            call_graph,
            test,
            code_region_sections,
        )?;
        lowerer.builder.declare_object(object).map_err(|e| {
            LowerError::Internal(format!(
                "failed to declare test object `{}`: {e}",
                test.object_name
            ))
        })?;
    }

    lowerer.lower_functions()?;
    Ok(lowerer.finish())
}

fn create_code_regions_object(
    lowerer: &mut ModuleLowerer<'_, '_>,
    funcs_by_symbol: &FxHashMap<&str, &MirFunction<'_>>,
    code_region_roots: &[String],
    code_region_sections: &FxHashMap<String, SectionName>,
    region_deps: &FxHashMap<String, FxHashSet<String>>,
) -> Result<Object, LowerError> {
    let object_name = ObjectName::from("CodeRegions");
    let mut sections = Vec::with_capacity(code_region_roots.len());

    for root in code_region_roots {
        let Some(_) = funcs_by_symbol.get(root.as_str()) else {
            return Err(LowerError::Internal(format!(
                "missing MIR function for code region root `{root}`"
            )));
        };
        let root_ref = *lowerer
            .name_map
            .get(root)
            .ok_or_else(|| LowerError::Internal(format!("unknown function: {root}")))?;

        let wrapper_name = format!("__fe_sonatina_code_region_entry_{}", sanitize_symbol(root));
        let runtime_metadata = lowerer
            .runtime_function_metadata
            .get(root)
            .cloned()
            .ok_or_else(|| {
                LowerError::Internal(format!("missing runtime type metadata for `{root}`"))
            })?;
        let wrapper_ref =
            lowerer.create_call_and_stop_wrapper(&wrapper_name, root_ref, &runtime_metadata)?;

        let section_name = code_region_sections
            .get(root)
            .cloned()
            .ok_or_else(|| LowerError::Internal(format!("missing section name for `{root}`")))?;

        let mut directives = vec![Directive::Entry(wrapper_ref)];

        let deps = region_deps.get(root).cloned().unwrap_or_default();
        let mut deps: Vec<String> = deps.into_iter().collect();
        deps.sort();
        for dep in deps {
            if dep == *root {
                continue;
            }
            let dep_section = code_region_sections.get(&dep).cloned().ok_or_else(|| {
                LowerError::Internal(format!(
                    "code region `{root}` depends on `{dep}`, but `{dep}` is not a known region root"
                ))
            })?;
            directives.push(Directive::Embed(Embed {
                source: SectionRef::Local(dep_section),
                as_symbol: EmbedSymbol::from(dep),
            }));
        }

        sections.push(Section {
            name: section_name,
            directives,
        });
    }

    Ok(Object {
        name: object_name,
        sections,
    })
}

fn create_test_object(
    lowerer: &mut ModuleLowerer<'_, '_>,
    funcs_by_symbol: &FxHashMap<&str, &MirFunction<'_>>,
    call_graph: &CallGraph,
    test: &TestInfo,
    code_region_sections: &FxHashMap<String, SectionName>,
) -> Result<Object, LowerError> {
    let Some(_) = funcs_by_symbol.get(test.symbol_name.as_str()) else {
        return Err(LowerError::Internal(format!(
            "missing MIR function for test `{}`",
            test.symbol_name
        )));
    };

    let test_ref = *lowerer
        .name_map
        .get(&test.symbol_name)
        .ok_or_else(|| LowerError::Internal(format!("unknown function: {}", test.symbol_name)))?;

    let wrapper_name = format!("__fe_sonatina_test_entry_{}", test.object_name);
    let runtime_metadata = lowerer
        .runtime_function_metadata
        .get(&test.symbol_name)
        .cloned()
        .ok_or_else(|| {
            LowerError::Internal(format!(
                "missing runtime type metadata for `{}`",
                test.symbol_name
            ))
        })?;
    let wrapper_ref =
        lowerer.create_call_and_stop_wrapper(&wrapper_name, test_ref, &runtime_metadata)?;

    let reachable = reachable_functions(call_graph, &test.symbol_name);
    let deps = collect_code_region_deps(&reachable, funcs_by_symbol);

    let mut directives = vec![Directive::Entry(wrapper_ref)];

    let code_regions_obj = ObjectName::from("CodeRegions");
    let mut deps: Vec<String> = deps.into_iter().collect();
    deps.sort();
    for dep in deps {
        let dep_section = code_region_sections.get(&dep).cloned().ok_or_else(|| {
            LowerError::Internal(format!(
                "test `{}` depends on code region `{dep}`, but `{dep}` is not a known region root",
                test.symbol_name
            ))
        })?;
        directives.push(Directive::Embed(Embed {
            source: SectionRef::External {
                object: code_regions_obj.clone(),
                section: dep_section,
            },
            as_symbol: EmbedSymbol::from(dep),
        }));
    }

    Ok(Object {
        name: ObjectName::from(test.object_name.clone()),
        sections: vec![Section {
            name: SectionName::from("runtime"),
            directives,
        }],
    })
}

impl<'db, 'a> ModuleLowerer<'db, 'a> {
    fn declare_functions_for_tests(
        &mut self,
        needed_symbols: &FxHashSet<String>,
    ) -> Result<(), LowerError> {
        for (idx, func) in self.mir.functions.iter().enumerate() {
            if func.symbol_name.is_empty() || !needed_symbols.contains(&func.symbol_name) {
                continue;
            }

            let name = &func.symbol_name;
            let (_sig, metadata) = self.lower_signature_and_metadata(func)?;
            let sig = metadata.signature(name, sonatina_ir::Linkage::Private);
            let func_ref = self.builder.declare_function(sig).map_err(|e| {
                LowerError::Internal(format!("failed to declare function {name}: {e}"))
            })?;
            self.apply_inline_hint(func_ref, func);

            self.func_map.insert(idx, func_ref);
            self.name_map.insert(name.clone(), func_ref);
            self.runtime_function_metadata
                .insert(name.clone(), metadata);
        }
        Ok(())
    }

    fn create_call_and_stop_wrapper(
        &mut self,
        wrapper_name: &str,
        callee_ref: sonatina_ir::module::FuncRef,
        runtime_metadata: &super::RuntimeFunctionMetadata,
    ) -> Result<sonatina_ir::module::FuncRef, LowerError> {
        if self.name_map.contains_key(wrapper_name) {
            return Err(LowerError::Internal(format!(
                "wrapper name collision: `{wrapper_name}`"
            )));
        }

        let sig = Signature::new(wrapper_name, sonatina_ir::Linkage::Private, &[], &[]);
        let func_ref = self.builder.declare_function(sig).map_err(|e| {
            LowerError::Internal(format!("failed to declare wrapper `{wrapper_name}`: {e}"))
        })?;

        let mut fb = self.builder.func_builder::<InstInserter>(func_ref);
        let is = self.isa.inst_set();

        let entry_block = fb.append_block();
        fb.switch_to_block(entry_block);

        let mut args = Vec::with_capacity(runtime_metadata.params.len());
        for arg_ty in runtime_metadata.params.iter().copied() {
            args.push(super::zero_value_for_type(&mut fb, arg_ty, is));
        }

        let call_inst = Call::new(is, callee_ref, args.into());
        if let Some(ret_ty) = runtime_metadata.ret {
            let _ = fb.insert_inst(call_inst, ret_ty);
        } else {
            fb.insert_inst_no_result(call_inst);
        }

        fb.insert_inst_no_result(EvmStop::new(is));
        fb.seal_all();
        fb.finish();

        Ok(func_ref)
    }
}

struct RuntimeCompileOutput {
    bytes: Vec<u8>,
    observability_json: Option<String>,
}

/// Compile all objects in the module at once so that shared functions are
/// lowered exactly once (avoiding accumulated mutations from repeated
/// `prepare_section` calls).
fn compile_all_objects_for_tests(
    module: &Module,
    options: SonatinaTestOptions,
) -> Result<Vec<ObjectArtifact>, LowerError> {
    let isa = super::create_evm_isa();
    let backend = EvmBackend::new(isa);

    let mut opts = CompileOptions::default();
    let mut verifier_cfg = VerifierConfig::for_level(VerificationLevel::Full);
    verifier_cfg.allow_detached_entities = true;
    opts.verifier_cfg = verifier_cfg;
    opts.emit_observability = options.emit_observability;

    compile_all_objects(module, &backend, &opts).map_err(|errors| {
        let msg = errors
            .iter()
            .map(|e| format!("{:?}", e))
            .collect::<Vec<_>>()
            .join("; ");
        LowerError::Internal(msg)
    })
}

/// Extract the runtime section for a specific object from pre-compiled artifacts.
fn extract_runtime_from_artifact(
    all_artifacts: &[ObjectArtifact],
    object_name: &str,
) -> Result<RuntimeCompileOutput, LowerError> {
    let artifact = all_artifacts
        .iter()
        .find(|a| a.object.0.as_str() == object_name)
        .ok_or_else(|| {
            LowerError::Internal(format!(
                "compiled object `{object_name}` not found in artifacts"
            ))
        })?;

    let section_name = SectionName::from("runtime");
    let runtime_section = artifact.sections.get(&section_name).ok_or_else(|| {
        LowerError::Internal(format!(
            "compiled object `{object_name}` has no runtime section"
        ))
    })?;
    let observability_json = artifact.observability_json();

    Ok(RuntimeCompileOutput {
        bytes: runtime_section.bytes.clone(),
        observability_json,
    })
}

fn wrap_as_init_code(runtime: &[u8]) -> Vec<u8> {
    // Minimal initcode:
    //   CODECOPY(0, <off>, <len>)
    //   RETURN(0, <len>)
    // with the runtime appended after the init.
    //
    // PUSHn <len>
    // PUSH2 <off>
    // PUSH1 0
    // CODECOPY
    // PUSHn <len>
    // PUSH1 0
    // RETURN
    fn push_u256(mut value: usize) -> Vec<u8> {
        let mut bytes = Vec::new();
        while value > 0 {
            bytes.push((value & 0xff) as u8);
            value >>= 8;
        }
        if bytes.is_empty() {
            bytes.push(0);
        }
        bytes.reverse();
        let n = bytes.len();
        debug_assert!((1..=32).contains(&n));
        let opcode = 0x5f + (n as u8);
        let mut out = Vec::with_capacity(1 + n);
        out.push(opcode);
        out.extend(bytes);
        out
    }

    let len_push = push_u256(runtime.len());

    let mut init = Vec::with_capacity(32 + runtime.len());
    init.extend(len_push.clone());
    init.push(0x61); // PUSH2
    let off_pos = init.len();
    init.extend([0u8, 0u8]); // filled in later
    init.extend([0x60, 0x00]); // PUSH1 0
    init.push(0x39); // CODECOPY
    init.extend(len_push);
    init.extend([0x60, 0x00]); // PUSH1 0
    init.push(0xf3); // RETURN

    let off = init.len();
    init[off_pos] = ((off >> 8) & 0xff) as u8;
    init[off_pos + 1] = (off & 0xff) as u8;

    init.extend_from_slice(runtime);
    init
}

#[cfg(test)]
mod regression_tests {
    use super::*;
    use common::InputDb;
    use std::fs;
    use std::path::PathBuf;
    use url::Url;

    fn temp_fixture_url(name: &str) -> Url {
        let fixture_path = std::env::temp_dir().join(name);
        Url::from_file_path(&fixture_path).expect("fixture path should be absolute")
    }

    #[test]
    fn erased_effect_params_do_not_reappear_as_pointer_runtime_args() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_erased_effect_params_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
pub contract C {
    init() {}
}

#[test]
fn smoke() {
    assert(true)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("erased effect params should remain erased in Sonatina test modules");
        assert_eq!(output.tests.len(), 1, "expected one runnable smoke test");
    }

    #[test]
    fn erased_generic_zst_params_do_not_reappear_in_runtime_signatures() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_erased_generic_zst_params_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
fn sum_three() -> u256 {
    let mut acc: u256 = 0
    for i in 0..3 {
        acc += i as u256
    }
    return acc
}

#[test]
fn smoke() {
    assert(sum_three() == 3)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("erased generic ZST params should remain erased in Sonatina signatures");
        assert_eq!(output.tests.len(), 1, "expected one runnable smoke test");
    }

    #[test]
    fn joined_scalar_ref_handles_that_spill_lower_without_panic() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_joined_scalar_ref_handles_spill_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
struct Data {
    x: u256,
    y: u256,
}

fn choose(_ flag: bool, _ d: ref Data) -> ref u256 {
    if flag {
        ref d.x
    } else {
        ref d.y
    }
}

#[test]
fn smoke() {
    let d = Data { x: 10, y: 20 }
    let picked = choose(true, ref d)
    assert(picked == d.x)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("joined scalar ref handles that spill should lower without panicking");
        assert_eq!(output.tests.len(), 1, "expected one runnable smoke test");
    }

    #[test]
    fn nested_scalar_handle_loads_and_copies_verify_in_test_modules() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_nested_scalar_handle_loads_and_copies_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
struct Reader {
    source: ref u256,
    bias: u256,
}

fn sum_reader(_ r: ref Reader) -> u256 {
    r.source + r.bias
}

fn pass_through(_ r: own Reader) -> Reader {
    r
}

#[test]
fn smoke() {
    let base = 7
    let reader = Reader {
        source: ref base,
        bias: 3,
    }
    let copy = pass_through(reader)
    assert(sum_reader(ref copy) == 10)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("nested scalar handle loads and copies should verify in Sonatina test modules");
        assert_eq!(output.tests.len(), 1, "expected one runnable smoke test");
    }

    #[test]
    fn wrapped_test_and_code_region_roots_are_not_forced_as_section_includes() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_test_object_include_roots_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
pub fn ping() -> u256 {
    return 1
}

#[test]
fn smoke() {
    assert(true)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ingot = top_mod.ingot(&db);
        let mir_module = lower_ingot(&db, ingot).expect("module should lower to MIR");
        let tests = collect_tests(&db, &mir_module.functions, None)
            .expect("test metadata collection should succeed");
        let call_graph = build_call_graph(&mir_module.functions);
        let funcs_by_symbol = build_funcs_by_symbol(&mir_module.functions);
        let code_region_roots = collect_code_region_roots(&mir_module.functions);
        let code_region_sections = code_region_roots
            .iter()
            .map(|sym| (sym.clone(), code_region_section_name(sym)))
            .collect::<FxHashMap<_, _>>();
        let mut region_reachable = FxHashMap::default();
        let mut region_deps = FxHashMap::default();
        for root in &code_region_roots {
            let reachable = reachable_functions(&call_graph, root);
            let deps = collect_code_region_deps(&reachable, &funcs_by_symbol);
            region_reachable.insert(root.clone(), reachable);
            region_deps.insert(root.clone(), deps);
        }

        let (needed_symbols, needed_code_regions) = collect_needed_symbols_for_tests(
            &tests,
            &call_graph,
            &funcs_by_symbol,
            &region_reachable,
            &region_deps,
        )
        .expect("test requirements should be collected");
        detect_code_region_cycles(&filter_code_region_graph(
            &needed_code_regions,
            &region_deps,
        ))
        .expect("region cycle detection should succeed");
        let module = compile_test_objects(
            &db,
            &mir_module,
            &tests,
            &needed_symbols,
            &needed_code_regions,
            &call_graph,
            &funcs_by_symbol,
            &code_region_sections,
            &region_deps,
        )
        .expect("test object compilation should succeed");

        let test_object = module
            .objects
            .values()
            .find(|object| object.name.0.as_str().starts_with("test_smoke"))
            .expect("test object should be present");
        let test_runtime = test_object
            .sections
            .iter()
            .find(|section| section.name.0.as_str() == "runtime")
            .expect("test runtime section should be present");
        assert!(
            test_runtime
                .directives
                .iter()
                .all(|directive| !matches!(directive, Directive::Include(_))),
            "test runtime should only root the wrapper entry: {test_runtime:?}"
        );

        if let Some(code_regions) = module.objects.get("CodeRegions") {
            for section in &code_regions.sections {
                assert!(
                    section
                        .directives
                        .iter()
                        .all(|directive| !matches!(directive, Directive::Include(_))),
                    "code region section `{}` should only root its wrapper entry: {section:?}",
                    section.name.0
                );
            }
        }
    }

    #[test]
    fn memory_ref_aggregate_params_lower_as_object_refs() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_memory_ref_aggregate_params_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
msg FooMsg {
    #[selector = 0x01]
    Run -> u256,
}

struct Mixer {}

impl Mixer {
    fn mix(_ input: [u256; 3]) -> [u256; 3] {
        let mut out: [u256; 3] = [0, 0, 0]
        for i in 0..3 {
            out[i] = input[i]
        }
        return out
    }
}

pub contract Foo {
    recv FooMsg {
        Run -> u256 {
            let out: [u256; 3] = Mixer::mix([1, 2, 3])
            return out[0] + out[1] + out[2]
        }
    }
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("module should lower to Sonatina IR");
        assert!(
            ir.contains("objref<"),
            "memory aggregate refs should lower as object refs:\n{ir}"
        );
    }

    #[test]
    fn compile_time_only_non_zst_params_do_not_reappear_in_runtime_signatures() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_compile_time_only_non_zst_params_test.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
const M: [[u256; 3]; 3] = [
    [2, 1, 1],
    [1, 2, 1],
    [1, 1, 2],
]

fn mix(_ state: [u256; 3]) -> [u256; 3] {
    let mut out: [u256; 3] = [0, 0, 0]
    for i in 0..3 {
        for j in 0..3 {
            out[i] = out[i] + M[i][j] + state[j]
        }
    }
    return out
}

#[test]
fn smoke() {
    let output: [u256; 3] = mix([1, 0, 0])
    assert(output[0] == 4)
    assert(output[1] == 3)
    assert(output[2] == 3)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("compile-time-only non-ZST params should stay erased in Sonatina signatures");
        assert_eq!(output.tests.len(), 1, "expected one runnable smoke test");
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

    #[test]
    fn filtered_test_run_ignores_unrelated_code_region_cycles() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_filtered_test_ignores_cycle.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
use std::evm::Evm

#[contract_init(A)]
fn a_init() uses (evm: mut Evm) {
    let len = evm.code_region_len(b_init)
    let offset = evm.code_region_offset(b_init)
    evm.codecopy(dest: 0, offset: offset, len: len)
    evm.return_data(offset: 0, len: len)
}

#[contract_init(B)]
fn b_init() uses (evm: mut Evm) {
    let len = evm.code_region_len(a_init)
    let offset = evm.code_region_offset(a_init)
    evm.codecopy(dest: 0, offset: offset, len: len)
    evm.return_data(offset: 0, len: len)
}

#[test]
fn keep() {
    assert(true)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let output = emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            Some("keep"),
        )
        .expect("filtered Sonatina test emission should ignore unrelated code-region cycles");

        assert_eq!(output.tests.len(), 1, "expected exactly one filtered test");
        assert_eq!(output.tests[0].hir_name, "keep");
    }

    #[test]
    fn tuple_encoder_reborrows_pointer_params_without_heap_spilling() {
        let mut db = DriverDataBase::default();
        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fe/tests/fixtures/fe_test/factory.fe");
        let fixture_source =
            fs::read_to_string(&fixture_path).expect("factory fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        let ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("module should lower to Sonatina IR");
        let start = ir
            .find("func private %_t0__t1__")
            .expect("tuple encoder helper should be present");
        let body = &ir[start
            ..ir[start..]
                .find("}\n\n")
                .map(|end| start + end + 1)
                .unwrap_or(ir.len())];

        assert!(
            !body.contains("evm_malloc 32.i256"),
            "tuple encoder helper should reuse the existing encoder pointer, not heap-spill it:\n{body}"
        );
    }

    #[test]
    fn branch_proven_nested_enum_variant_loads_survive_o2_test_codegen() {
        let mut db = DriverDataBase::default();
        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fe/tests/fixtures/fe_test/if_let_while_let.fe");
        let fixture_source =
            fs::read_to_string(&fixture_path).expect("if_let_while_let fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O2,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("branch-proven nested enum payload loads should verify after O2 test lowering");
    }

    #[test]
    fn specialized_storage_handle_enum_tags_verify_in_test_modules() {
        let mut db = DriverDataBase::default();
        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fe/tests/fixtures/fe_test/option_mut_scalar_match_regression.fe");
        let fixture_source = fs::read_to_string(&fixture_path)
            .expect("option_mut_scalar_match_regression fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("storage-specialized enum-tag temps should verify in Sonatina test modules");
    }

    #[test]
    fn transparent_scalar_newtype_borrows_verify_in_test_modules() {
        let mut db = DriverDataBase::default();
        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fe/tests/fixtures/fe_test/ref_scalar_nested.fe");
        let fixture_source = fs::read_to_string(&fixture_path)
            .expect("ref_scalar_nested fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("transparent scalar newtype borrows should verify in Sonatina test modules");
    }

    #[test]
    fn pointer_like_wrapper_handles_verify_in_test_modules() {
        let mut db = DriverDataBase::default();
        let fixture_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../fe/tests/fixtures/fe_test/view_param_local_ref_take_reverse.fe");
        let fixture_source = fs::read_to_string(&fixture_path)
            .expect("view_param_local_ref_take_reverse fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);

        emit_test_module_sonatina(
            &db,
            top_mod,
            OptLevel::O0,
            SonatinaTestOptions::default(),
            None,
        )
        .expect("pointer-like wrapper handles should verify in Sonatina test modules");
    }

    #[test]
    fn structural_type_cache_skips_irrelevant_pointer_metadata() {
        let mut db = DriverDataBase::default();
        let fixture_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/match_tuple.fe");
        let fixture_source =
            fs::read_to_string(&fixture_path).expect("match_tuple fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let tuple_ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("match_tuple should lower to Sonatina IR");
        assert_eq!(
            tuple_ir.matches("type @__fe_obj_tuple_").count(),
            2,
            "tuple lowering should reuse the same specialized object tuple types:\n{tuple_ir}"
        );

        let mut db = DriverDataBase::default();
        let fixture_path =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/effect_ptr_domains.fe");
        let fixture_source = fs::read_to_string(&fixture_path)
            .expect("effect_ptr_domains fixture should be readable");
        let file_url = Url::from_file_path(&fixture_path).expect("fixture path should be absolute");
        db.workspace()
            .touch(&mut db, file_url.clone(), Some(fixture_source));
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let effect_ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("effect_ptr_domains should lower to Sonatina IR");
        assert_eq!(
            effect_ir.matches("type @__fe_Foo_").count(),
            1,
            "storage pointer lowering should not create duplicate non-object Foo types:\n{effect_ir}"
        );
        assert_eq!(
            effect_ir.matches("type @__fe_obj_Foo_").count(),
            1,
            "memory object lowering should not create duplicate object Foo types:\n{effect_ir}"
        );
    }

    #[test]
    fn static_typed_allocations_lower_to_obj_alloc() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_static_typed_allocations_lower_to_obj_alloc.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
msg FooMsg {
    #[selector = 0x01]
    Run -> u256,
}

struct Builders {}

impl Builders {
    fn make_a() -> [u256; 3] {
        return [1, 2, 3]
    }

    fn make_sum() -> u256 {
        let a: [u256; 3] = Builders::make_a()
        return a[0] + a[1] + a[2]
    }
}

pub contract Foo {
    recv FooMsg {
        Run -> u256 {
            Builders::make_sum()
        }
    }
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("module should lower to Sonatina IR");
        assert!(
            ir.contains("obj.alloc"),
            "expected object allocations:\n{ir}"
        );
        assert!(
            !ir.contains("alloca [i256; 3]"),
            "typed array allocations must not lower through alloca:\n{ir}"
        );
    }

    #[test]
    fn dynamic_alloc_stays_on_evm_malloc() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_dynamic_alloc_stays_on_evm_malloc.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
pub contract Foo {
    init(seed: u256) {}
}

#[test]
fn allocates_dynamic_init_args() uses (evm: mut Evm) {
    let addr = evm.create2<Foo>(value: 0, args: (1,), salt: 0)
    assert(addr.inner != 0)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ir = crate::emit_module_sonatina_ir_optimized(&db, top_mod, OptLevel::O0, None)
            .expect("module should lower to Sonatina IR");

        assert!(
            ir.contains("evm_malloc"),
            "dynamic raw allocations must still lower through evm_malloc:\n{ir}"
        );
    }

    #[test]
    fn test_module_prunes_unreachable_functions_and_omits_empty_code_regions_object() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_test_module_prunes_reachability.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
fn keep() -> bool {
    return true
}

fn drop_helper() -> bool {
    return false
}

#[test]
fn smoke() {
    assert(keep())
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ingot = top_mod.ingot(&db);
        let mir_module = lower_ingot(&db, ingot).expect("lowering should succeed");

        let tests = collect_tests(&db, &mir_module.functions, None)
            .expect("test metadata collection should succeed");
        assert_eq!(tests.len(), 1, "expected exactly one filtered test");

        let call_graph = build_call_graph(&mir_module.functions);
        let funcs_by_symbol = build_funcs_by_symbol(&mir_module.functions);
        let code_region_roots = collect_code_region_roots(&mir_module.functions);
        let code_region_sections = code_region_roots
            .iter()
            .map(|sym| (sym.clone(), code_region_section_name(sym)))
            .collect::<FxHashMap<_, _>>();

        let mut region_reachable: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        let mut region_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        for root in &code_region_roots {
            let reachable = reachable_functions(&call_graph, root);
            let deps = collect_code_region_deps(&reachable, &funcs_by_symbol);
            region_reachable.insert(root.clone(), reachable);
            region_deps.insert(root.clone(), deps);
        }

        let (needed_symbols, needed_code_regions) = collect_needed_symbols_for_tests(
            &tests,
            &call_graph,
            &funcs_by_symbol,
            &region_reachable,
            &region_deps,
        )
        .expect("test requirements should be collected");
        detect_code_region_cycles(&filter_code_region_graph(
            &needed_code_regions,
            &region_deps,
        ))
        .expect("region cycle detection should succeed");
        let module = compile_test_objects(
            &db,
            &mir_module,
            &tests,
            &needed_symbols,
            &needed_code_regions,
            &call_graph,
            &funcs_by_symbol,
            &code_region_sections,
            &region_deps,
        )
        .expect("test object lowering should succeed");

        let lowered_names: FxHashSet<String> = module
            .funcs()
            .iter()
            .map(|func| module.ctx.func_sig(*func, |sig| sig.name().to_string()))
            .collect();
        let keep_symbol = mir_module
            .functions
            .iter()
            .find(|func| func.symbol_name.contains("keep"))
            .map(|func| func.symbol_name.clone())
            .expect("keep symbol should exist");
        let drop_symbol = mir_module
            .functions
            .iter()
            .find(|func| func.symbol_name.contains("drop_helper"))
            .map(|func| func.symbol_name.clone())
            .expect("drop_helper symbol should exist");

        assert!(
            lowered_names.contains(&keep_symbol),
            "reachable helper should be lowered"
        );
        assert!(
            !lowered_names.contains(&drop_symbol),
            "unreachable helper should not be lowered"
        );
        assert!(
            !module.objects.contains_key("CodeRegions"),
            "test module should not emit an empty CodeRegions object"
        );
    }

    #[test]
    fn test_collect_needed_symbols_includes_transitive_code_region_dependencies() {
        let mut db = DriverDataBase::default();
        let file_url = temp_fixture_url("sonatina_test_module_code_region_transitive_deps.fe");
        db.workspace().touch(
            &mut db,
            file_url.clone(),
            Some(
                r#"
msg CounterMsg {
    #[selector = 0xd09de08a]
    Increment,
    #[selector = 0x6d4ce63c]
    Get -> u256,
}

struct CounterStore {
    value: u256,
}

pub contract Counter {
    mut store: CounterStore

    init() uses (mut store) {
        store.value = 0
    }

    recv CounterMsg {
        Increment uses (mut store) {
            store.value = store.value + 1
        }

        Get -> u256 uses (store) {
            store.value
        }
    }
}

#[test]
fn smoke() uses (evm: mut Evm) {
    let addr = evm.create2<Counter>(value: 0, args: (), salt: 0)
    assert(addr.inner != 0)
}
"#
                .to_string(),
            ),
        );
        let file = db
            .workspace()
            .get(&db, &file_url)
            .expect("file should be loaded");
        let top_mod = db.top_mod(file);
        let ingot = top_mod.ingot(&db);
        let mir_module = lower_ingot(&db, ingot).expect("lowering should succeed");

        let tests = collect_tests(&db, &mir_module.functions, Some("smoke"))
            .expect("test metadata collection should succeed");
        assert_eq!(tests.len(), 1, "expected exactly one filtered test");

        let call_graph = build_call_graph(&mir_module.functions);
        let funcs_by_symbol = build_funcs_by_symbol(&mir_module.functions);
        let code_region_roots = collect_code_region_roots(&mir_module.functions);
        let init_root = code_region_roots
            .iter()
            .find(|sym| sym.contains("Counter_init"))
            .expect("Counter init code region should exist")
            .clone();
        let runtime_root = code_region_roots
            .iter()
            .find(|sym| sym.contains("Counter_runtime"))
            .expect("Counter runtime code region should exist")
            .clone();

        let mut region_reachable: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        let mut region_deps: FxHashMap<String, FxHashSet<String>> = FxHashMap::default();
        for root in &code_region_roots {
            let reachable = reachable_functions(&call_graph, root);
            let deps = collect_code_region_deps(&reachable, &funcs_by_symbol);
            region_reachable.insert(root.clone(), reachable);
            region_deps.insert(root.clone(), deps);
        }

        let (_needed_symbols, needed_code_regions) = collect_needed_symbols_for_tests(
            &tests,
            &call_graph,
            &funcs_by_symbol,
            &region_reachable,
            &region_deps,
        )
        .expect("needed symbol collection should succeed");

        assert!(
            needed_code_regions.contains(&init_root),
            "directly referenced init code region should be included"
        );
        assert!(
            needed_code_regions.contains(&runtime_root),
            "transitive runtime code region dependency should be included"
        );
    }
}
