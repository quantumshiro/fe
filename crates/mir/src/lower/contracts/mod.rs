use common::ingot::Ingot;
use hir::{
    analysis::diagnostics::SpannedHirAnalysisDb,
    hir_def::{Contract, HirIngot, TopLevelMod},
};

mod emit;
mod handlers;
mod plan;
mod symbols;
mod target;

pub(super) use super::{MirBuilder, MirLowerError, MirLowerResult, diagnostics};

use emit::ContractEmitter;
use plan::ContractPlan;
use target::TargetContext;

pub struct ContractLoweringConfig<'a> {
    pub ingot_prefix: Option<&'a str>,
    pub defer_all_roots: bool,
}

pub(super) fn lower_contract_templates<'db>(
    db: &'db dyn SpannedHirAnalysisDb,
    top_mod: TopLevelMod<'db>,
) -> MirLowerResult<Vec<crate::ir::MirFunction<'db>>> {
    let contracts = top_mod.all_contracts(db);
    if contracts.is_empty() {
        return Ok(Vec::new());
    }

    let target = TargetContext::new(db, top_mod)?;
    let config = ContractLoweringConfig {
        ingot_prefix: None,
        defer_all_roots: false,
    };
    let mut out = Vec::new();
    for &contract in contracts {
        out.extend(lower_single_contract(&target, db, contract, &config)?);
    }
    Ok(out)
}

pub(super) fn lower_dependency_contract_templates<'db>(
    db: &'db dyn SpannedHirAnalysisDb,
    host_top_mod: TopLevelMod<'db>,
    dep_ingot: Ingot<'db>,
    dep_name: &str,
) -> MirLowerResult<Vec<crate::ir::MirFunction<'db>>> {
    let target = TargetContext::new(db, host_top_mod)?;
    let config = ContractLoweringConfig {
        ingot_prefix: Some(dep_name),
        defer_all_roots: true,
    };
    let mut out = Vec::new();
    for &dep_mod in dep_ingot.all_modules(db).iter() {
        for &contract in dep_mod.all_contracts(db) {
            out.extend(lower_single_contract(&target, db, contract, &config)?);
        }
    }
    Ok(out)
}

fn lower_single_contract<'db>(
    target: &TargetContext<'db>,
    db: &'db dyn SpannedHirAnalysisDb,
    contract: Contract<'db>,
    config: &ContractLoweringConfig<'_>,
) -> MirLowerResult<Vec<crate::ir::MirFunction<'db>>> {
    let plan = ContractPlan::build(db, target, contract, config)?;
    ContractEmitter::new(db, target, config).emit_program(&plan)
}
