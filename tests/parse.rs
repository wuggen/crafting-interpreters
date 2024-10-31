use std::path::PathBuf;
use std::str::FromStr;

use insta::assert_snapshot;
use tlox::diag::render::render_dcx;
use tlox::parse::parse_source;
use tlox::session::SessionKey;
use tlox::syn::SynEq;

use super::*;

const FILTER_VAR: &str = "PARSE_TESTS_FILTER";
const TESTS_PATH: &str = "parse";

fn parse_test_err(key: SessionKey, case: TestCase) {
    let TestCase { name, content } = case;
    let idx = key.get().sm.add_source(name.as_str(), &content);

    if let Some(res) = parse_source(key, idx) {
        panic!("{name} parsed without error:\n{res}");
    }

    assert!(
        key.get().dcx.has_errors(),
        "dcx has no errors after failing to parse {name}"
    );

    insta::with_settings!({
        description => content,
    }, {
        assert_snapshot!(name, render_dcx())
    });
}

fn parse_test_success(key: SessionKey, case: TestCase) {
    let TestCase { name, content } = case;
    let idx = key.get().sm.add_source(name.as_str(), &content);
    let first_parse = parse_source(key, idx)
        .or_else(|| panic!("failed to parse {name}"))
        .unwrap();

    insta::with_settings!({
        description => content,
    }, {
        assert_snapshot!(name.as_str(), first_parse);
    });

    let first_parse_printed = first_parse.to_string();
    let idx = key.get().sm.add_source(name.as_str(), &first_parse_printed);
    let reparse = parse_source(key, idx)
        .or_else(|| panic!("failed to reparse {name} after pretty-printing"))
        .unwrap();

    assert!(
        first_parse.syn_eq(&reparse),
        "{name} failed reparse check\n::First::\n{first_parse}\n\n::Reparse::\n{reparse}"
    );
    assert!(
        !key.get().dcx.has_errors(),
        "dcx has errors after {name}:\n{}",
        render_dcx()
    );
}

#[test]
fn parse_tests() {
    FileTests {
        base_path: PathBuf::from_str(TESTS_PATH).unwrap(),
        filter_var: FILTER_VAR,
        test_fn: parse_test_success,
        err_test_fn: parse_test_err,
    }
    .run();
}
