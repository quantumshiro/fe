use fe_hir::hir_def::{InlineAttrErrorKind, Partial, Stmt};
use fe_hir::test_db::HirAnalysisTestDb;

#[test]
fn expr_valued_inline_attr_stays_invalid() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "inline_attr_expr_value.fe".into(),
        r#"#[inline = 1 + 2]
fn bad() {}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let funcs = top_mod.all_funcs(&db);
    let [func] = funcs.as_slice() else {
        panic!("expected exactly one function");
    };

    assert_eq!(func.inline_hint(&db), None);
    assert_eq!(
        func.inline_attr_error(&db),
        Some(InlineAttrErrorKind::InvalidForm)
    );
}

#[test]
fn empty_inline_attr_parens_stay_invalid() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "inline_attr_empty_parens.fe".into(),
        r#"#[inline()]
fn bad() {}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let funcs = top_mod.all_funcs(&db);
    let [func] = funcs.as_slice() else {
        panic!("expected exactly one function");
    };

    assert_eq!(func.inline_hint(&db), None);
    assert_eq!(
        func.inline_attr_error(&db),
        Some(InlineAttrErrorKind::InvalidForm)
    );
}

#[test]
fn expr_valued_loop_unroll_attr_does_not_apply_hint() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "loop_unroll_expr_value.fe".into(),
        r#"fn bad(xs: [u256; 1]) {
    #[unroll = 1 + 2]
    for x in xs {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let funcs = top_mod.all_funcs(&db);
    let [func] = funcs.as_slice() else {
        panic!("expected exactly one function");
    };
    let body = func.body(&db).expect("expected function body");

    let unroll_hint = body.stmts(&db).iter().find_map(|(_, stmt)| match stmt {
        Partial::Present(Stmt::For(_, _, _, hint)) => Some(*hint),
        Partial::Present(_) | Partial::Absent => None,
    });

    assert_eq!(unroll_hint, Some(None));
}

#[test]
fn empty_loop_unroll_attr_parens_do_not_apply_hint() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "loop_unroll_empty_parens.fe".into(),
        r#"fn bad(xs: [u256; 1]) {
    #[unroll()]
    for x in xs {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let funcs = top_mod.all_funcs(&db);
    let [func] = funcs.as_slice() else {
        panic!("expected exactly one function");
    };
    let body = func.body(&db).expect("expected function body");

    let unroll_hint = body.stmts(&db).iter().find_map(|(_, stmt)| match stmt {
        Partial::Present(Stmt::For(_, _, _, hint)) => Some(*hint),
        Partial::Present(_) | Partial::Absent => None,
    });

    assert_eq!(unroll_hint, Some(None));
}

#[test]
fn unroll_never_attr_prevents_unrolling() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "loop_unroll_never.fe".into(),
        r#"fn bad(xs: [u256; 1]) {
    #[unroll(never)]
    for x in xs {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let funcs = top_mod.all_funcs(&db);
    let [func] = funcs.as_slice() else {
        panic!("expected exactly one function");
    };
    let body = func.body(&db).expect("expected function body");

    let unroll_hint = body.stmts(&db).iter().find_map(|(_, stmt)| match stmt {
        Partial::Present(Stmt::For(_, _, _, hint)) => Some(*hint),
        Partial::Present(_) | Partial::Absent => None,
    });

    assert_eq!(unroll_hint, Some(Some(false)));
}

#[test]
fn empty_payable_attr_parens_do_not_mark_init_payable() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "payable_init_empty_parens.fe".into(),
        r#"contract C {
    #[payable()]
    init() {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let contracts = top_mod.all_contracts(&db);
    let [contract] = contracts.as_slice() else {
        panic!("expected exactly one contract");
    };
    let init = contract.init(&db).expect("expected contract init");

    assert!(!init.is_payable(&db));
}

#[test]
fn invalid_payable_init_attr_does_not_mark_init_payable() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "payable_init_invalid.fe".into(),
        r#"contract C {
    #[payable = 1]
    init() {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let contracts = top_mod.all_contracts(&db);
    let [contract] = contracts.as_slice() else {
        panic!("expected exactly one contract");
    };
    let init = contract.init(&db).expect("expected contract init");

    assert!(!init.is_payable(&db));
}

#[test]
fn malformed_payable_does_not_mask_valid_init_payable_attr() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "payable_init_mixed_validity.fe".into(),
        r#"contract C {
    #[payable(foo)]
    #[payable]
    init() {}
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let contracts = top_mod.all_contracts(&db);
    let [contract] = contracts.as_slice() else {
        panic!("expected exactly one contract");
    };
    let init = contract.init(&db).expect("expected contract init");

    assert!(init.is_payable(&db));
}

#[test]
fn invalid_payable_recv_arm_attr_does_not_mark_arm_payable() {
    let mut db = HirAnalysisTestDb::default();
    let file = db.new_stand_alone(
        "payable_recv_arm_invalid.fe".into(),
        r#"use std::abi::sol

msg M {
    #[selector = sol("ping()")]
    Ping,
}

contract C {
    recv M {
        #[payable(foo)]
        Ping {} {}
    }
}"#,
    );
    let (top_mod, _) = db.top_mod(file);
    let contracts = top_mod.all_contracts(&db);
    let [contract] = contracts.as_slice() else {
        panic!("expected exactly one contract");
    };
    let arm = contract
        .recv_arm(&db, 0, 0)
        .expect("expected one recv arm at 0:0");

    assert!(!arm.is_payable(&db));
}
