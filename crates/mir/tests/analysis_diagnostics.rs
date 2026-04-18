use common::InputDb;
use driver::DriverDataBase;
use fe_mir::{
    MirDiagnosticsMode, MirLowerError, ValueOrigin, collect_mir_diagnostics, lower_module,
};
use url::Url;

#[test]
fn lower_module_reports_analysis_diagnostics_as_error() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///analysis_diagnostics.fe").unwrap();
    let src = r#"
pub fn mismatched_ret() -> bool {
    1
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let err = lower_module(&db, top_mod).expect_err("analysis diagnostics should fail lowering");

    let MirLowerError::AnalysisDiagnostics {
        func_name,
        diagnostics,
    } = err
    else {
        panic!("expected AnalysisDiagnostics, got {err:?}");
    };

    assert!(!func_name.is_empty(), "func name is empty");
    assert!(diagnostics.contains("type mismatch"));
}

#[test]
fn collect_mir_diagnostics_short_circuits_on_invalid_hir() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///analysis_diagnostics_in_monomorphization.fe").unwrap();
    let src = r#"
fn foo(x: u8) -> u256 {
    x
}

#[test]
fn bar_test() {
    foo(42)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let output = collect_mir_diagnostics(&db, top_mod, MirDiagnosticsMode::CompilerParity);
    assert!(
        output.internal_errors.is_empty(),
        "expected invalid HIR to skip MIR entirely, got: {:?}",
        output.internal_errors
    );
    assert!(output.diagnostics.is_empty());
}

#[test]
fn lower_module_rejects_unsupported_const_path_match_patterns() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///unsupported_const_path_pattern.fe").unwrap();
    let src = r#"
const FOO: String<3> = "foo"

pub fn test(x: String<3>) -> u8 {
    match x {
        FOO => 0
        _ => 1
    }
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let err = lower_module(&db, top_mod).expect_err("unsupported const-path pattern should fail");

    let MirLowerError::Unsupported { message, .. } = err else {
        panic!("expected Unsupported, got {err:?}");
    };
    assert!(
        message.contains("pattern"),
        "expected unsupported-pattern error, got `{message}`",
    );
}

#[test]
fn lower_module_rejects_unsupported_string_literal_match_patterns() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///unsupported_string_literal_pattern.fe").unwrap();
    let src = r#"
pub fn test(x: String<3>) -> u8 {
    match x {
        "foo" => 0
        _ => 1
    }
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let err =
        lower_module(&db, top_mod).expect_err("unsupported string literal pattern should fail");

    let MirLowerError::Unsupported { message, .. } = err else {
        panic!("expected Unsupported, got {err:?}");
    };
    assert!(
        message.contains("pattern"),
        "expected unsupported-pattern error, got `{message}`",
    );
}

#[test]
fn lower_module_reports_or_pattern_binding_errors_as_analysis_diagnostics() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///or_pattern_binding_error.fe").unwrap();
    let src = r#"
enum E {
    A(u8),
    B,
}

pub fn test(e: E) -> u8 {
    match e {
        E::A(x) | E::B => x
    }
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let err = lower_module(&db, top_mod).expect_err("binding or-pattern should fail analysis");

    let MirLowerError::AnalysisDiagnostics { diagnostics, .. } = err else {
        panic!("expected AnalysisDiagnostics, got {err:?}");
    };
    assert!(
        diagnostics.contains("bindings in `|` patterns are not supported"),
        "expected binding-or-pattern diagnostic, got `{diagnostics}`",
    );
}

#[test]
fn lower_module_reports_const_array_materialization_failures_as_unsupported() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///const_array_materialization_unsupported.fe").unwrap();
    let src = r#"
const BIG: [String<64>; 1] = [
    "This is a long string that exceeds thirty-two bytes in length!!",
]

pub fn bad() -> String<64> {
    BIG[0]
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);

    let err = lower_module(&db, top_mod).expect_err("const-array materialization should fail");

    let MirLowerError::Unsupported { func_name, message } = err else {
        panic!("expected Unsupported, got {err:?}");
    };

    assert!(func_name.contains("bad"), "func name is {func_name}");
    assert!(
        message.contains("failed to materialize const"),
        "message is {message}"
    );
    assert!(message.contains("String<64>"), "message is {message}");
}

#[test]
fn lower_module_materializes_large_string_literal_via_const_region() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///large_string_literal_unsupported.fe").unwrap();
    let src = r#"
pub fn bad() -> String<64> {
    "This is a long string that exceeds thirty-two bytes in length!!"
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let module = lower_module(&db, top_mod).expect("large string literal should lower");
    assert!(
        module
            .functions
            .iter()
            .flat_map(|func| func.body.values.iter())
            .any(|value| matches!(value.origin, ValueOrigin::ConstRegion(_)))
    );
}

#[test]
fn lower_module_materializes_large_const_string_via_const_region() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///large_const_string_unsupported.fe").unwrap();
    let src = r#"
const BIG: String<64> = "This is a long string that exceeds thirty-two bytes in length!!"

pub fn bad() -> String<64> {
    BIG
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    let module = lower_module(&db, top_mod).expect("large const string should lower");
    assert!(
        module
            .functions
            .iter()
            .flat_map(|func| func.body.values.iter())
            .any(|value| matches!(value.origin, ValueOrigin::ConstRegion(_)))
    );
}

#[test]
fn lower_module_supports_builtin_seq_methods_on_const_generic_arrays() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///builtin_seq_const_generic_array.fe").unwrap();
    let src = r#"
use core::seq::Seq

pub fn root(values: [u256; 5]) -> u256 {
    values.get(0)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    lower_module(&db, top_mod).expect("built-in const-generic array methods should lower");
}

#[test]
fn lower_module_supports_encode_methods_on_const_generic_arrays() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///encode_const_generic_array.fe").unwrap();
    let src = r#"
use core::abi::Encode
use std::abi::Sol

pub fn root(values: [bool; 5]) {
    values.encode_to_ptr(0)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    lower_module(&db, top_mod).expect("Encode<Sol> array methods should lower");
}

#[test]
fn lower_module_supports_generic_direct_encode_on_const_generic_arrays() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///generic_direct_encode_const_generic_array.fe").unwrap();
    let src = r#"
use core::abi::Encode
use std::abi::Sol

fn direct<T: Encode<Sol>>(_: T) -> bool {
    T::DIRECT_ENCODE
}

pub fn root(values: [bool; 5]) -> bool {
    direct(values)
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    lower_module(&db, top_mod).expect("generic DIRECT_ENCODE paths should lower");
}

#[test]
fn lower_module_supports_generic_trait_methods_on_const_generic_arrays() {
    let mut db = DriverDataBase::default();
    let url = Url::parse("file:///generic_trait_method_const_generic_array.fe").unwrap();
    let src = r#"
trait Flag<A> {
    fn flag(self) -> bool
}

struct Marker {}

impl Flag<Marker> for bool {
    fn flag(self) -> bool {
        self
    }
}

impl<T, A, const N: usize> Flag<A> for [T; N]
    where T: Flag<A> + Copy
{
    fn flag(self) -> bool {
        self[0].flag()
    }
}

pub fn root(values: [bool; 5]) -> bool {
    values.flag()
}
"#;

    let file = db.workspace().touch(&mut db, url, Some(src.to_string()));
    let top_mod = db.top_mod(file);
    lower_module(&db, top_mod).expect("generic trait array methods should lower");
}
