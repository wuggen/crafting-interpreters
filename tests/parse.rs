use std::any::Any;
use std::fs::{self, DirEntry};
use std::path::PathBuf;

use insta::assert_snapshot;
use tlox::diag::render::render_dcx;
use tlox::parse::parse_source;
use tlox::session::Session;
use tlox::syn::SynEq;

const PARSE_TESTS_PATH: &str = "tests/parse";
const SNAPSHOTS_PATH: &str = "parse/snapshots";

fn file_parse_test(path: PathBuf) {
    let name = path.file_name().unwrap().to_str().unwrap();
    let content = fs::read_to_string(&path)
        .inspect_err(|_| eprintln!("error reading {}", path.display()))
        .unwrap();

    if name.starts_with("err_") {
        file_parse_test_err(path, &content);
    } else {
        file_parse_test_success(path, &content);
    }
}

fn file_parse_test_err(path: PathBuf, content: &str) {
    Session::with_default(|key| {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let idx = key.get().sm.add_source(path, content);

        parse_source(key, idx).map(|res| panic!("{name} parsed without error:\n{res}"));
        assert!(
            key.get().dcx.has_errors(),
            "dcx has no errors after failing to parse {name}"
        );

        insta::with_settings!({
            description => content,
            snapshot_path => SNAPSHOTS_PATH,
        }, {
            assert_snapshot!(name.to_string(), render_dcx())
        });
    })
}

fn file_parse_test_success(path: PathBuf, content: &str) {
    Session::with_default(|key| {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let idx = key.get().sm.add_source(path, content);
        let first_parse = parse_source(key, idx)
            .or_else(|| panic!("failed to parse {name}"))
            .unwrap();

        insta::with_settings!({
            description => content,
            snapshot_path => SNAPSHOTS_PATH,
        }, {
            assert_snapshot!(name.as_str(), first_parse);
        });

        let first_parse_printed = first_parse.to_string();
        let idx = key.get().sm.add_source(name.clone(), &first_parse_printed);
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
    })
}

fn collect_tests() -> impl Iterator<Item = PathBuf> {
    fn match_file(entry: DirEntry) -> Option<PathBuf> {
        if !entry.file_type().unwrap().is_file() {
            return None;
        }

        if let Ok(filter) = std::env::var("PARSE_TEST_FILTER") {
            if !entry.path().to_str().unwrap().contains(&filter) {
                return None;
            }
        }

        let name = entry.file_name();
        if name.to_str().unwrap().ends_with(".lx") {
            Some(entry.path())
        } else {
            None
        }
    }

    fs::read_dir(PARSE_TESTS_PATH)
        .unwrap()
        .filter_map(Result::ok)
        .filter_map(match_file)
}

#[test]
fn parse_tests() {
    let mut cause: Option<Box<dyn Any + Send>> = None;

    for path in collect_tests() {
        if let Err(c) = std::panic::catch_unwind(|| {
            file_parse_test(path);
        }) {
            cause = Some(c);
        }
    }

    if let Some(cause) = cause {
        std::panic::resume_unwind(cause);
    }
}
