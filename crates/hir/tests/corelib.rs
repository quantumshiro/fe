use common::InputDb;
use common::stdlib::{HasBuiltinCore, HasBuiltinStd};
use driver::{DriverDataBase, db::DiagnosticsCollection};
use fe_hir::analysis::ty::{
    trait_resolution::{GoalSatisfiability, TraitSolveCx, is_goal_satisfiable},
    ty_check::check_func_body,
};
use fe_hir::hir_def::{Expr, LitKind, Partial};
use url::Url;

#[cfg(target_arch = "wasm32")]
use test_utils::url_utils::UrlExt;

#[test]
fn analyze_corelib() {
    let db = DriverDataBase::default();
    let core = db.builtin_core();

    let core_diags = db.run_on_ingot(core);
    assert_builtin_clean(&db, core_diags, "core");
}

#[test]
fn analyze_stdlib() {
    let db = DriverDataBase::default();
    let std_ingot = db.builtin_std();

    let std_diags = db.run_on_ingot(std_ingot);
    assert_builtin_clean(&db, std_diags, "std");
}

fn assert_builtin_clean(db: &DriverDataBase, diags: DiagnosticsCollection<'_>, name: &str) {
    if diags.is_empty() {
        return;
    }

    diags.emit(db);
    panic!(
        "expected no diagnostics for builtin {name}, but got:\n{}",
        diags.format_diags(db)
    );
}

#[test]
fn solver_proves_encode_for_fixed_bool_arrays() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///encode_fixed_bool_array_goal.fe").unwrap();
    let src = r#"
use core::abi::Encode
use std::abi::Sol

pub fn root(values: [bool; 5]) {
    values.encode_to_ptr(0)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let diags = db.run_on_top_mod(top_mod);
    assert!(
        diags.is_empty(),
        "unexpected diagnostics: {}",
        diags.format_diags(&db)
    );

    let func = top_mod.all_funcs(&db)[0];
    let body = func.body(&db).expect("root should have a body");
    let typed_body = &check_func_body(&db, func).1;
    let callable = body
        .exprs(&db)
        .keys()
        .find_map(|expr| {
            let callable = typed_body.callable_expr(expr)?;
            let name = callable.callable_def.name(&db)?;
            (name.data(&db) == "encode_to_ptr").then_some(callable)
        })
        .expect("encode_to_ptr callable should resolve during type checking");
    let inst = callable
        .trait_inst()
        .expect("encode_to_ptr should be a trait method");
    let solve_cx = TraitSolveCx::new(&db, func.scope());

    match is_goal_satisfiable(&db, solve_cx, inst) {
        GoalSatisfiability::Satisfied(_) => {}
        other => panic!(
            "expected `{}` to be satisfiable, got {other:?}",
            inst.pretty_print(&db, true)
        ),
    }
}

#[test]
fn string_literals_can_pick_up_dynstring_api_from_later_use() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///string_dynstring_api.fe").unwrap();
    let src = r#"
pub fn root() -> u8 {
    let text = "hello-dynamic-api"
    text.view().byte_at(0)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let diags = db.run_on_top_mod(top_mod);
    assert!(
        diags.is_empty(),
        "unexpected diagnostics: {}",
        diags.format_diags(&db)
    );

    let func = top_mod.all_funcs(&db)[0];
    let body = func.body(&db).expect("root should have a body");
    let typed_body = &check_func_body(&db, func).1;
    let literal_expr = body
        .exprs(&db)
        .keys()
        .find(|expr| {
            matches!(
                expr.data(&db, body),
                Partial::Present(Expr::Lit(LitKind::String(_)))
            )
        })
        .expect("string literal should be present");

    assert_eq!(
        typed_body.expr_ty(&db, literal_expr).pretty_print(&db),
        "DynString"
    );
}

#[test]
fn runtime_string_literals_can_infer_dynstring_from_return_type() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///string_runtime_return_dynstring.fe").unwrap();
    let src = r#"
use std::abi::Text

pub fn root() -> Text {
    let text = "hello-runtime-return"
    text
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let diags = db.run_on_top_mod(top_mod);
    assert!(
        diags.is_empty(),
        "unexpected diagnostics: {}",
        diags.format_diags(&db)
    );

    let func = top_mod.all_funcs(&db)[0];
    let body = func.body(&db).expect("root should have a body");
    let typed_body = &check_func_body(&db, func).1;
    let literal_expr = body
        .exprs(&db)
        .keys()
        .find(|expr| {
            matches!(
                expr.data(&db, body),
                Partial::Present(Expr::Lit(LitKind::String(_)))
            )
        })
        .expect("string literal should be present");

    assert_eq!(
        typed_body.expr_ty(&db, literal_expr).pretty_print(&db),
        "DynString"
    );
}

#[test]
fn runtime_sol_selector_still_accepts_string_literals() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///runtime_sol_selector.fe").unwrap();
    let src = r#"
use std::abi::sol

pub fn root() -> u32 {
    let signature = "ping()"
    let selector = sol(signature)
    selector
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let diags = db.run_on_top_mod(top_mod);
    assert!(
        diags.is_empty(),
        "unexpected diagnostics: {}",
        diags.format_diags(&db)
    );
}
