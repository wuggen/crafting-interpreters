use std::fmt::Write;
use std::path::PathBuf;

use insta::assert_snapshot;
use tlox::diag::render::render_dcx;
use tlox::eval::Interpreter;
use tlox::parse::parse_source;
use tlox::session::SessionKey;

use super::*;

const FILTER_VAR: &str = "EVAL_TESTS_FILTER";
const TESTS_PATH: &str = "eval";

fn eval_test(key: SessionKey, case: TestCase) -> (String, String) {
    let TestCase { name, content } = case;
    let idx = key.get().sm.add_source(name.as_str(), &content);
    let program = parse_source(key, idx).unwrap_or_else(|| {
        panic!("{name} failed to parse. Diags:\n{}", render_dcx());
    });

    let mut output = Vec::new();
    let mut interp = Interpreter::new(key).with_vec_output(&mut output);
    interp.eval(&program);
    drop(interp);

    let output = String::from_utf8(output).unwrap();
    let diagnostics = if key.get().dcx.has_errors() {
        render_dcx()
    } else {
        String::new()
    };

    let combined = combine_output_diags(&output, &diagnostics);

    insta::with_settings!({
        description => content,
    }, {
        assert_snapshot!(name, combined);
    });

    (output, diagnostics)
}

fn combine_output_diags(output: &str, diags: &str) -> String {
    let mut res = String::new();

    if !output.is_empty() {
        write!(res, ":: Output ::\n{output}").unwrap();
    }

    if !diags.is_empty() {
        if !output.is_empty() {
            write!(res, "\n\n").unwrap();
        }

        write!(res, ":: Diagnostics ::\n{diags}").unwrap();
    }

    res
}

fn eval_test_err(key: SessionKey, case: TestCase) {
    let name = case.name.clone();
    let (_, diags) = eval_test(key, case);
    assert!(!diags.is_empty(), "{name} did not generate diagnostics");
}

fn eval_test_success(key: SessionKey, case: TestCase) {
    let name = case.name.clone();
    let (_, diags) = eval_test(key, case);
    assert!(diags.is_empty(), "{name} generated diagnostics");
}

#[test]
fn eval_tests() {
    FileTests {
        base_path: PathBuf::from(TESTS_PATH),
        filter_var: FILTER_VAR,
        test_fn: eval_test_success,
        err_test_fn: eval_test_err,
    }
    .run();
}
