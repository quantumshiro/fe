# Traversal API Refactor — Briefing

This project incrementally replaces raw HIR access + ad‑hoc `lower_*` calls with a semantic traversal API. Work proceeds in small, verifiable steps to keep snapshots stable and tests green.

## Modules
- `hir_def::semantic`
  - Externally facing, semantic helpers on HIR items (e.g., `Func::return_ty`, `Impl::ty`, `TypeAlias::ty`).
  - Returns semantic IDs (`TyId`, `TraitInstId`, …) and small aggregations. Does not expose raw syntax.
  - Callers across analysis/diagnostics should prefer these methods.

- `hir_def::temporary_syntactic_hir_shim`
  - Temporary, public wrappers around newly `pub(super)` syntactic fields/methods.
  - Only for the visitor and other in-progress areas that still need raw syntax while we migrate.
  - Naming convention: `___tmp` suffix (e.g., `type_ref___tmp`). The module has a local `#![allow(non_snake_case)]`.
  - Do not add new dependencies on this module unless strictly necessary; delete usages as soon as consumers are migrated to `semantic`.

## Refactoring Modes
- Semantic surfacing
  - Add minimal, high-value item methods in `semantic` that return semantic IDs or small aggregates.
  - Examples: `Func::return_ty`, `Impl::ty`, `ImplTrait::ty`, `Const::ty`, `TypeAlias::ty`.

- Ablation (privatize syntax)
  - Make raw syntactic fields/methods `pub(super)` in `hir_def::item`.
  - Provide a temporary wrapper in the shim with `___tmp` for any caller not yet migrated.

- Consumer rewiring
  - Replace direct field reads and `lower_hir_ty` calls with semantic methods.
  - Where migration is not yet possible, use the shim’s `___tmp` methods.

- Reduction of analysis queries (e.g., `lower_hir_ty`)
  - `lower_hir_ty` is just one example among many analysis queries we want to tuck behind (or factor/dissolve into) public semantic methods. The same applies to other `lower_*`, `resolve_*`, and helper queries across `analysis`.
  - Introduce semantic item helpers or context‑rich views so consumers no longer perform raw lowering/imperative assembly. Replace loops over syntax with owner‑aware methods.
  - Target patterns to dissolve: large queries that imperatively build intermediate structs, manually accumulate context, and cache bits ad‑hoc. Instead, factor out reusable routines into small, composable methods on items/views.

- Cleanup
  - Remove shim usages once consumers rely on `semantic` only.
  - Delete obsolete helpers, enum owners, and duplicated analysis paths once parity is proven.

## Views (context‑rich wrappers)
- Definition
  - A “view” wraps a traversable owner (e.g., an item or `ScopeId`) together with the minimal syntactic handle needed, offering semantic methods that apply in that context.
  - Examples (future and partial today): `FieldView`, `WherePredicateView`, `TraitAssocTypeView`.

- When to use a view vs. a plain method
  - Use a plain item method when you can return a single semantic value without coupling to child context.
  - Use a view when child semantics depend on the owner’s scope/assumptions (e.g., bounds, defaults, satisfiability), or when you need a stable handle to iterate children while preserving owner context.

- Goals
  - Reduce imperative “constructor” queries that bundle context and syntax manually.
  - Centralize lowering/normalization/validation logic behind concise, discoverable methods.
  - Keep layering clean: callers don’t see raw syntax or ad‑hoc caches; they see semantic IDs and small typed aggregations.

## Workflow Checklist (per change)
1) Identify a raw syntactic read or `lower_*` usage in a consumer.
2) Add/extend a semantic method in `hir_def::semantic` that returns the needed semantic value(s).
3) Flip the underlying syntactic field/method in `hir_def::item` to `pub(super)`.
4) If needed, add a `___tmp` wrapper in `temporary_syntactic_hir_shim` and point the visitor (or other holdouts) to it.
5) Rewire the consumer to call the semantic method; fall back to the shim only where migration is deferred.
6) Run `cargo test --workspace`. Keep snapshots stable; do not relax diagnostics.
7) Repeat on the next smallest surface.

## Naming & Conventions
- Semantic methods: concise and semantic (e.g., `return_ty`, `trait_inst`). No “syntax” in names.
- Shim methods: `___tmp` suffix (e.g., `type_ref___tmp`, `ret_type_ref___tmp`, `field_type_ref___tmp`).
- Do not widen visibility of raw fields; prefer `pub(super)` + shim.

## Salsa considerations
- Tracked queries need concrete key types; avoid putting tracked functions directly on traits.
- If a generic capability needs a tracked query, prefer a simple enum key or split per‑type queries, and keep the traversal API (traits/views) as the public surface.
- Keep keys deterministic and layering stable; views should call tracked functions under the hood but remain untracked themselves.

## Test Discipline
- Run `env -u RUSTC_WRAPPER cargo test --workspace` between steps.
- Snapshot tests are authoritative; avoid double-reporting or changing spans/messages unless explicitly intended.

## Removal Plan
- The shim is a transitional module. As semantic coverage expands and callers migrate, delete `___tmp` usages and then remove the wrappers and finally the module.

## Quick Grep Aids
- Find raw lowerings: `rg -n "\blower_hir_ty\(" crates`.
- Find tmp shims: `rg -n "___tmp\b" crates`.
- Find raw field accessors: search `type_ref(db)` or specific fields after flipping to `pub(super)`.
