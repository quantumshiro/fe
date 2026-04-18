use hir::{
    analysis::{HirAnalysisDb, ty::ty_def::TyId},
    hir_def::EnumVariant,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    CoreLib, MirProjection, MirProjectionPath,
    ir::{AddressSpaceKind, PointerInfo},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PointerInfoConflict<'db> {
    pub path: crate::MirProjectionPath<'db>,
    pub existing: PointerInfo<'db>,
    pub incoming: PointerInfo<'db>,
}

pub(crate) fn normalize_pointer_leaf_info_entries<'db>(
    entries: impl IntoIterator<Item = (crate::MirProjectionPath<'db>, PointerInfo<'db>)>,
) -> Result<Vec<(crate::MirProjectionPath<'db>, PointerInfo<'db>)>, PointerInfoConflict<'db>> {
    let mut merged: FxHashMap<crate::MirProjectionPath<'db>, PointerInfo<'db>> =
        FxHashMap::default();
    for (path, info) in entries {
        let Some(existing) = merged.get(&path).copied() else {
            merged.insert(path, info);
            continue;
        };
        if existing == info {
            continue;
        }
        let merged_address_space = match (existing.address_space, info.address_space) {
            (lhs, rhs) if lhs == rhs => lhs,
            (AddressSpaceKind::Memory, rhs) => rhs,
            (lhs, AddressSpaceKind::Memory) => lhs,
            _ => {
                return Err(PointerInfoConflict {
                    path,
                    existing,
                    incoming: info,
                });
            }
        };
        let merged_target_ty = match (existing.target_ty, info.target_ty) {
            (lhs, rhs) if lhs == rhs => lhs,
            (Some(lhs), None) => Some(lhs),
            (None, Some(rhs)) => Some(rhs),
            _ => {
                return Err(PointerInfoConflict {
                    path,
                    existing,
                    incoming: info,
                });
            }
        };
        merged.insert(
            path,
            PointerInfo {
                address_space: merged_address_space,
                target_ty: merged_target_ty,
            },
        );
    }
    let mut out: Vec<_> = merged.into_iter().collect();
    out.sort_by_cached_key(|(path, _)| format!("{path:?}"));
    Ok(out)
}

struct PointerLeafInfoCollector<'a, 'db> {
    db: &'db dyn HirAnalysisDb,
    core: &'a CoreLib<'db>,
    default_space: AddressSpaceKind,
    out: Vec<(MirProjectionPath<'db>, PointerInfo<'db>)>,
    active: FxHashSet<TyId<'db>>,
}

impl<'a, 'db> PointerLeafInfoCollector<'a, 'db> {
    fn new(
        db: &'db dyn HirAnalysisDb,
        core: &'a CoreLib<'db>,
        default_space: AddressSpaceKind,
    ) -> Self {
        Self {
            db,
            core,
            default_space,
            out: Vec::new(),
            active: FxHashSet::default(),
        }
    }

    fn collect(&mut self, ty: TyId<'db>, prefix: &MirProjectionPath<'db>) {
        if !self.active.insert(ty) {
            return;
        }

        if let Some(info) =
            crate::repr::handle_pointer_info_for_ty(self.db, self.core, ty, self.default_space)
        {
            self.out.push((prefix.clone(), info));
            if let Some((_, inner)) = ty.as_capability(self.db) {
                self.collect(inner, prefix);
            }
        } else if let Some((_, inner)) = ty.as_capability(self.db) {
            self.collect(inner, prefix);
        } else if let Some(inner) = crate::repr::transparent_newtype_field_ty(self.db, ty) {
            self.collect(inner, prefix);
        } else if let Some(enum_def) = ty.as_enum(self.db) {
            for (idx, variant_def) in enum_def.variants(self.db).enumerate() {
                let variant = EnumVariant::new(enum_def, idx);
                for (field_idx, field_ty) in variant_def
                    .field_tys(self.db)
                    .into_iter()
                    .map(|field_ty| field_ty.instantiate(self.db, ty.generic_args(self.db)))
                    .enumerate()
                {
                    let mut field_prefix = prefix.clone();
                    field_prefix.push(MirProjection::VariantField {
                        variant,
                        enum_ty: ty,
                        field_idx,
                    });
                    self.collect(field_ty, &field_prefix);
                }
            }
        } else {
            for (idx, field_ty) in ty.field_types(self.db).iter().copied().enumerate() {
                let mut field_prefix = prefix.clone();
                field_prefix.push(MirProjection::Field(idx));
                self.collect(field_ty, &field_prefix);
            }
        }

        self.active.remove(&ty);
    }
}

pub(crate) fn pointer_leaf_paths_for_ty<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
) -> Vec<MirProjectionPath<'db>> {
    pointer_leaf_infos_for_ty_with_default(db, core, ty, AddressSpaceKind::Memory)
        .into_iter()
        .map(|(path, _)| path)
        .collect()
}

pub(crate) fn pointer_leaf_infos_for_ty_with_default<'db>(
    db: &'db dyn HirAnalysisDb,
    core: &CoreLib<'db>,
    ty: TyId<'db>,
    default_space: AddressSpaceKind,
) -> Vec<(MirProjectionPath<'db>, PointerInfo<'db>)> {
    let mut collector = PointerLeafInfoCollector::new(db, core, default_space);
    collector.collect(ty, &MirProjectionPath::new());
    collector.out
}

#[cfg(test)]
mod tests {
    use common::InputDb;
    use driver::DriverDataBase;
    use hir::projection::Projection;
    use url::Url;

    use super::*;
    use hir::test_db::TestDb;

    #[test]
    fn memory_then_non_memory_promotes_to_non_memory() {
        let root = crate::MirProjectionPath::new();
        let entries = vec![
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: None,
                },
            ),
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            ),
        ];
        let normalized = normalize_pointer_leaf_info_entries(entries).expect("no conflict");
        assert_eq!(
            normalized,
            vec![(
                root,
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            )]
        );
    }

    #[test]
    fn non_memory_then_memory_keeps_non_memory() {
        let root = crate::MirProjectionPath::new();
        let entries = vec![
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Calldata,
                    target_ty: None,
                },
            ),
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: None,
                },
            ),
        ];
        let normalized = normalize_pointer_leaf_info_entries(entries).expect("no conflict");
        assert_eq!(
            normalized,
            vec![(
                root,
                PointerInfo {
                    address_space: AddressSpaceKind::Calldata,
                    target_ty: None,
                },
            )]
        );
    }

    #[test]
    fn conflicting_non_memory_spaces_error() {
        let root = crate::MirProjectionPath::new();
        let entries = vec![
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Storage,
                    target_ty: None,
                },
            ),
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Calldata,
                    target_ty: None,
                },
            ),
        ];
        let conflict = normalize_pointer_leaf_info_entries(entries).expect_err("must conflict");
        assert_eq!(conflict.path, root);
        assert_eq!(conflict.existing.address_space, AddressSpaceKind::Storage);
        assert_eq!(conflict.incoming.address_space, AddressSpaceKind::Calldata);
    }

    #[test]
    fn prefers_known_target_ty() {
        let db = TestDb::default();
        let ty = hir::analysis::ty::ty_def::TyId::new(
            &db,
            hir::analysis::ty::ty_def::TyData::TyBase(hir::analysis::ty::ty_def::TyBase::Prim(
                hir::analysis::ty::ty_def::PrimTy::U256,
            )),
        );
        let root = crate::MirProjectionPath::new();
        let entries = vec![
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: None,
                },
            ),
            (
                root.clone(),
                PointerInfo {
                    address_space: AddressSpaceKind::Memory,
                    target_ty: Some(ty),
                },
            ),
        ];
        let normalized = normalize_pointer_leaf_info_entries(entries).expect("no conflict");
        assert_eq!(normalized[0].1.target_ty, Some(ty));
    }

    #[test]
    fn repeated_field_types_keep_distinct_pointer_leaf_paths() {
        let mut db = DriverDataBase::default();
        let url =
            Url::parse("file:///repeated_field_types_keep_distinct_pointer_leaf_paths.fe").unwrap();
        let src = r#"
struct Wrapper {
    value: mut u256
}

struct Pair {
    left: Wrapper,
    right: Wrapper
}

fn use_pair(pair: Pair) {}
"#;
        let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
        let top_mod = db.top_mod(file);
        let pair_ty = top_mod
            .all_funcs(&db)
            .iter()
            .copied()
            .find(|func| {
                func.name(&db)
                    .to_opt()
                    .is_some_and(|name| name.data(&db) == "use_pair")
            })
            .and_then(|func| func.params(&db).next())
            .map(|param| param.ty(&db))
            .expect("use_pair parameter should exist");
        let core = CoreLib::new(&db, top_mod.scope());
        let paths = pointer_leaf_paths_for_ty(&db, &core, pair_ty);

        assert_eq!(
            paths,
            vec![
                MirProjectionPath::from_projection(Projection::Field(0)),
                MirProjectionPath::from_projection(Projection::Field(1)),
            ]
        );
    }

    #[test]
    fn transparent_pointer_like_wrapper_targets_use_runtime_layout() {
        let mut db = DriverDataBase::default();
        let url =
            Url::parse("file:///transparent_pointer_like_wrapper_targets_use_runtime_layout.fe")
                .unwrap();
        let src = r#"
struct ReverseArr {
    base: ref [u256; 8],
}

struct TakeReverseArr {
    n: usize,
    base: ref ReverseArr,
}

fn use_take(t: TakeReverseArr) {}
"#;
        let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
        let top_mod = db.top_mod(file);
        let take_ty = top_mod
            .all_funcs(&db)
            .iter()
            .copied()
            .find(|func| {
                func.name(&db)
                    .to_opt()
                    .is_some_and(|name| name.data(&db) == "use_take")
            })
            .and_then(|func| func.params(&db).next())
            .map(|param| param.ty(&db))
            .expect("use_take parameter should exist");
        let core = CoreLib::new(&db, top_mod.scope());
        let infos =
            pointer_leaf_infos_for_ty_with_default(&db, &core, take_ty, AddressSpaceKind::Memory);

        let info = infos
            .iter()
            .find(|(path, _)| *path == MirProjectionPath::from_projection(Projection::Field(1)))
            .expect("expected root pointer leaf info for `TakeReverseArr.base`");
        assert_eq!(info.1.address_space, AddressSpaceKind::Memory);
        assert_eq!(
            info.1
                .target_ty
                .expect("pointer leaf info should preserve pointee type")
                .pretty_print(&db),
            "[u256; 8]"
        );
    }

    #[test]
    fn transparent_storage_handle_wrapper_targets_use_runtime_layout() {
        let mut db = DriverDataBase::default();
        let url =
            Url::parse("file:///transparent_storage_handle_wrapper_targets_use_runtime_layout.fe")
                .unwrap();
        let src = r#"
struct Cell {
    value: u256,
}

struct CellMover {
    cell: mut Cell,
}

fn use_mover(m: mut CellMover) {}
"#;
        let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
        let top_mod = db.top_mod(file);
        let mover_ty = top_mod
            .all_funcs(&db)
            .iter()
            .copied()
            .find(|func| {
                func.name(&db)
                    .to_opt()
                    .is_some_and(|name| name.data(&db) == "use_mover")
            })
            .and_then(|func| func.params(&db).next())
            .map(|param| param.ty(&db))
            .expect("use_mover parameter should exist");
        let core = CoreLib::new(&db, top_mod.scope());
        let infos = normalize_pointer_leaf_info_entries(pointer_leaf_infos_for_ty_with_default(
            &db,
            &core,
            mover_ty,
            AddressSpaceKind::Storage,
        ))
        .expect("transparent storage handle wrapper should not conflict");

        assert_eq!(
            infos.len(),
            1,
            "transparent storage wrapper should collapse to one root leaf"
        );
        assert_eq!(infos[0].0, MirProjectionPath::new());
        assert_eq!(infos[0].1.address_space, AddressSpaceKind::Storage);
        assert_eq!(
            infos[0]
                .1
                .target_ty
                .expect("pointer leaf info should preserve pointee type")
                .pretty_print(&db),
            "Cell"
        );
    }
}
