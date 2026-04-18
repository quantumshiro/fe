use common::{indexmap::IndexMap, ingot::IngotKind};
use hir::{
    analysis::{
        HirAnalysisDb,
        name_resolution::{PathRes, resolve_path},
        ty::{
            const_eval::{ConstValue, try_eval_const_body},
            corelib::resolve_core_trait,
            normalize::normalize_ty,
            trait_def::TraitInstId,
            trait_def::assoc_const_body_for_trait_inst,
            trait_resolution::{PredicateListId, TraitSolveCx},
            ty_def::TyId,
        },
    },
    hir_def::{Func, IdentId, PathId, TopLevelMod, Trait, scope_graph::ScopeId},
};
use num_bigint::BigUint;

use super::{MirLowerError, MirLowerResult};

pub(super) struct TargetContext<'db> {
    pub host: TargetHostContext<'db>,
    pub abi: AbiContext<'db>,
}

pub(super) struct TargetHostContext<'db> {
    pub root_effect_ty: TyId<'db>,
    pub contract_host_inst: TraitInstId<'db>,
    pub init_input_ty: TyId<'db>,
    pub input_ty: TyId<'db>,
    pub input_byte_input_inst: TraitInstId<'db>,
    pub effect_handle_trait: Trait<'db>,
    pub effect_handle_from_raw_fn: Func<'db>,
    pub input_fn: Func<'db>,
    pub field_fn: Func<'db>,
    pub init_field_fn: Func<'db>,
    pub byte_input_len_fn: Func<'db>,
    pub runtime_selector_fn: Func<'db>,
    pub runtime_decoder_fn: Func<'db>,
    pub return_value_fn: Func<'db>,
    pub return_unit_fn: Func<'db>,
    pub abort_fn: Func<'db>,
}

pub(super) struct AbiContext<'db> {
    pub abi_ty: TyId<'db>,
    pub abi_inst: TraitInstId<'db>,
    pub selector_ty: TyId<'db>,
    pub selector_size: BigUint,
    pub init_decoder_ty: TyId<'db>,
    pub runtime_decoder_ty: TyId<'db>,
    pub abi_decoder_new: Func<'db>,
    pub decode_trait: Trait<'db>,
    pub decode_decode: Func<'db>,
}

const EVM_TARGET_TY_PATH: &[&str] = &["std", "evm", "EvmTarget"];

#[derive(Clone, Copy)]
struct TargetSpec {
    target_ty_path: &'static [&'static str],
}

impl TargetSpec {
    const EVM: Self = Self {
        target_ty_path: EVM_TARGET_TY_PATH,
    };
}

impl<'db> TargetContext<'db> {
    pub(super) fn new(
        db: &'db dyn HirAnalysisDb,
        top_mod: TopLevelMod<'db>,
    ) -> MirLowerResult<Self> {
        Self::for_target(db, top_mod, TargetSpec::EVM)
    }

    fn for_target(
        db: &'db dyn HirAnalysisDb,
        top_mod: TopLevelMod<'db>,
        spec: TargetSpec,
    ) -> MirLowerResult<Self> {
        let scope = top_mod.scope();
        let assumptions = PredicateListId::empty_list(db);
        let (host, default_abi_ty) = TargetHostContext::new(db, top_mod, scope, assumptions, spec)?;
        let abi = AbiContext::new(db, scope, assumptions, default_abi_ty, &host)?;
        Ok(Self { host, abi })
    }
}

impl<'db> TargetHostContext<'db> {
    fn new(
        db: &'db dyn HirAnalysisDb,
        top_mod: TopLevelMod<'db>,
        scope: ScopeId<'db>,
        assumptions: PredicateListId<'db>,
        spec: TargetSpec,
    ) -> MirLowerResult<(Self, TyId<'db>)> {
        let target_ty = resolve_ty_path(db, top_mod, scope, spec.target_ty_path)?;
        let target_trait =
            resolve_core_trait(db, scope, &["contracts", "Target"]).ok_or_else(|| {
                MirLowerError::Unsupported {
                    func_name: "<contract lowering>".into(),
                    message: "missing core trait `contracts::Target`".into(),
                }
            })?;
        let inst_target = TraitInstId::new(db, target_trait, vec![target_ty], IndexMap::new());
        let root_effect_ty = resolve_assoc_ty(db, inst_target, scope, assumptions, "RootEffect");
        let default_abi_ty = resolve_assoc_ty(db, inst_target, scope, assumptions, "DefaultAbi");

        let contract_host_trait = resolve_core_trait(db, scope, &["contracts", "ContractHost"])
            .ok_or_else(|| MirLowerError::Unsupported {
                func_name: "<contract lowering>".into(),
                message: "missing core trait `contracts::ContractHost`".into(),
            })?;
        let contract_host_inst = TraitInstId::new(
            db,
            contract_host_trait,
            vec![root_effect_ty],
            IndexMap::new(),
        );

        let init_input_ty =
            resolve_assoc_ty(db, contract_host_inst, scope, assumptions, "InitInput");
        let input_ty = resolve_assoc_ty(db, contract_host_inst, scope, assumptions, "Input");
        let byte_input_trait =
            resolve_core_trait(db, scope, &["abi", "ByteInput"]).ok_or_else(|| {
                MirLowerError::Unsupported {
                    func_name: "<contract lowering>".into(),
                    message: "missing core trait `abi::ByteInput`".into(),
                }
            })?;
        let input_byte_input_inst =
            TraitInstId::new(db, byte_input_trait, vec![input_ty], IndexMap::new());

        let effect_handle_trait = resolve_core_trait(db, scope, &["effect_ref", "EffectHandle"])
            .expect("missing required core trait `core::effect_ref::EffectHandle`");
        let effect_handle_from_raw = require_trait_method(db, effect_handle_trait, "from_raw")?;

        let host = Self {
            root_effect_ty,
            contract_host_inst,
            init_input_ty,
            input_ty,
            input_byte_input_inst,
            effect_handle_trait,
            effect_handle_from_raw_fn: effect_handle_from_raw,
            input_fn: require_trait_method(db, contract_host_trait, "input")?,
            field_fn: require_trait_method(db, contract_host_trait, "field")?,
            init_field_fn: require_trait_method(db, contract_host_trait, "init_field")?,
            byte_input_len_fn: require_trait_method(db, byte_input_trait, "len")?,
            runtime_selector_fn: require_trait_method(db, contract_host_trait, "runtime_selector")?,
            runtime_decoder_fn: require_trait_method(db, contract_host_trait, "runtime_decoder")?,
            return_value_fn: require_trait_method(db, contract_host_trait, "return_value")?,
            return_unit_fn: require_trait_method(db, contract_host_trait, "return_unit")?,
            abort_fn: require_trait_method(db, contract_host_trait, "abort")?,
        };

        Ok((host, default_abi_ty))
    }
}

impl<'db> AbiContext<'db> {
    fn new(
        db: &'db dyn HirAnalysisDb,
        scope: ScopeId<'db>,
        assumptions: PredicateListId<'db>,
        abi_ty: TyId<'db>,
        host: &TargetHostContext<'db>,
    ) -> MirLowerResult<Self> {
        let abi_trait = resolve_core_trait(db, scope, &["abi", "Abi"]).ok_or_else(|| {
            MirLowerError::Unsupported {
                func_name: "<contract lowering>".into(),
                message: "missing core trait `abi::Abi`".into(),
            }
        })?;
        let abi_inst = TraitInstId::new(db, abi_trait, vec![abi_ty], IndexMap::new());
        let selector_ty = resolve_assoc_ty(db, abi_inst, scope, assumptions, "Selector");
        let selector_size_name = IdentId::new(db, "SELECTOR_SIZE".to_string());
        let solve_cx = TraitSolveCx::new(db, scope).with_assumptions(assumptions);
        let selector_size_body =
            assoc_const_body_for_trait_inst(db, solve_cx, abi_inst, selector_size_name)
                .ok_or_else(|| MirLowerError::Unsupported {
                    func_name: "<contract lowering>".into(),
                    message: format!(
                        "missing evaluable associated const `SELECTOR_SIZE` for ABI `{}`",
                        abi_ty.pretty_print(db)
                    ),
                })?;
        let selector_size = match try_eval_const_body(db, selector_size_body, TyId::u256(db)) {
            Some(ConstValue::Int(value)) => value,
            _ => {
                return Err(MirLowerError::Unsupported {
                    func_name: "<contract lowering>".into(),
                    message: format!(
                        "failed to evaluate associated const `SELECTOR_SIZE` for ABI `{}`",
                        abi_ty.pretty_print(db)
                    ),
                });
            }
        };

        let decoder_ctor = resolve_assoc_ty(db, abi_inst, scope, assumptions, "Decoder");
        let init_decoder_ty = normalize_ty(
            db,
            TyId::app(db, decoder_ctor, host.init_input_ty),
            scope,
            assumptions,
        );
        let runtime_decoder_ty = normalize_ty(
            db,
            TyId::app(db, decoder_ctor, host.input_ty),
            scope,
            assumptions,
        );

        let abi_decoder_new = require_trait_method(db, abi_trait, "decoder_new")?;
        let decode_trait = resolve_core_trait(db, scope, &["abi", "Decode"]).ok_or_else(|| {
            MirLowerError::Unsupported {
                func_name: "<contract lowering>".into(),
                message: "missing core trait `abi::Decode`".into(),
            }
        })?;

        Ok(Self {
            abi_ty,
            abi_inst,
            selector_ty,
            selector_size,
            init_decoder_ty,
            runtime_decoder_ty,
            abi_decoder_new,
            decode_trait,
            decode_decode: require_trait_method(db, decode_trait, "decode")?,
        })
    }
}

fn resolve_assoc_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    inst: TraitInstId<'db>,
    scope: ScopeId<'db>,
    assumptions: PredicateListId<'db>,
    name: &str,
) -> TyId<'db> {
    let ident = IdentId::new(db, name.to_owned());
    normalize_ty(db, TyId::assoc_ty(db, inst, ident), scope, assumptions)
}

fn require_trait_method<'db>(
    db: &'db dyn HirAnalysisDb,
    trait_def: Trait<'db>,
    name: &str,
) -> MirLowerResult<Func<'db>> {
    let name_id = IdentId::new(db, name.to_string());
    trait_def
        .methods(db)
        .find(|func| func.name(db).to_opt() == Some(name_id))
        .ok_or_else(|| MirLowerError::Unsupported {
            func_name: "<contract lowering>".into(),
            message: format!(
                "missing core trait method `{}` on `{}`",
                name,
                trait_def
                    .name(db)
                    .to_opt()
                    .map(|id| id.data(db).to_string())
                    .unwrap_or_else(|| "<anonymous trait>".into())
            ),
        })
}

fn resolve_ty_path<'db>(
    db: &'db dyn HirAnalysisDb,
    top_mod: TopLevelMod<'db>,
    scope: ScopeId<'db>,
    segments: &[&str],
) -> MirLowerResult<TyId<'db>> {
    let path = path_from_segments(db, top_mod, segments);
    let assumptions = PredicateListId::empty_list(db);
    match resolve_path(db, path, scope, assumptions, false) {
        Ok(PathRes::Ty(ty) | PathRes::TyAlias(_, ty)) => Ok(ty),
        Ok(other) => Err(MirLowerError::Unsupported {
            func_name: "<contract lowering>".into(),
            message: format!(
                "expected type at path `{}` but resolved to `{}`",
                path.pretty_print(db),
                other.kind_name()
            ),
        }),
        Err(err) => Err(MirLowerError::Unsupported {
            func_name: "<contract lowering>".into(),
            message: format!(
                "failed to resolve type path `{}`: {err:?}",
                path.pretty_print(db)
            ),
        }),
    }
}

fn path_from_segments<'db>(
    db: &'db dyn HirAnalysisDb,
    top_mod: TopLevelMod<'db>,
    segments: &[&str],
) -> PathId<'db> {
    let ingot_kind = top_mod.ingot(db).kind(db);
    let mut iter = segments.iter();
    let root = iter
        .next()
        .unwrap_or_else(|| panic!("expected non-empty path segments"));
    let root_ident = match (*root, ingot_kind) {
        ("core", IngotKind::Core) => IdentId::make_ingot(db),
        ("core", _) => IdentId::make_core(db),
        ("std", IngotKind::Std) => IdentId::make_ingot(db),
        ("std", _) => IdentId::new(db, "std".to_string()),
        (other, _) => IdentId::new(db, other.to_string()),
    };
    let mut path = PathId::from_ident(db, root_ident);
    for seg in iter {
        path = path.push_ident(db, IdentId::new(db, (*seg).to_string()));
    }
    path
}
