use std::fmt::Write;
use std::fs::{self, DirEntry};
use std::panic::UnwindSafe;
use std::path::{Path, PathBuf};

use tlox::session::{Session, SessionKey};

mod eval;
mod parse;

pub struct FileTests<F, E> {
    pub base_path: PathBuf,
    pub filter_var: &'static str,
    pub test_fn: F,
    pub err_test_fn: E,
}

pub struct TestCase {
    pub name: String,
    pub content: String,
}

impl<F, E> FileTests<F, E>
where
    F: Fn(SessionKey, TestCase),
    E: Fn(SessionKey, TestCase),
    for<'a> &'a F: UnwindSafe,
    for<'a> &'a E: UnwindSafe,
{
    pub fn run(&self) {
        let paths = collect_files(&self.base_path).collect::<Vec<_>>();

        let mut snap_path = self.base_path.clone();
        snap_path.push("snapshots");

        let filter = std::env::var(self.filter_var).unwrap_or_default();
        let mut failures = String::new();

        insta::with_settings!({
            snapshot_path => snap_path,
        }, {
            for path in paths {
                if let Err(new_failures) = file_test(path, &self.test_fn, &self.err_test_fn, &filter) {
                    failures.push_str(&new_failures);
                }
            }
        });

        if !failures.is_empty() {
            std::panic::resume_unwind(Box::new(failures));
        }
    }
}

pub fn collect_files(base_path: &Path) -> impl Iterator<Item = PathBuf> + use<> {
    let filter_fn = move |entry: DirEntry| {
        if !entry.file_type().unwrap().is_file() {
            return None;
        }

        let name = entry.file_name();
        if name.to_str().unwrap().ends_with(".lx") {
            Some(entry.path())
        } else {
            None
        }
    };

    fs::read_dir(base_path)
        .unwrap()
        .filter_map(Result::ok)
        .filter_map(filter_fn)
}

pub fn collect_cases_from_file<'a>(
    base_name: &'a str,
    file_content: &'a str,
    filter: &'a str,
) -> impl Iterator<Item = TestCase> {
    let mut name = String::from(base_name);
    let mut content = String::new();
    let mut lines = file_content.lines();
    let base_iter = std::iter::from_fn(move || {
        let mut ignore = false;
        for line in lines.by_ref() {
            if ignore {
                if line.starts_with("//ENDIGNORE") {
                    ignore = false;
                }

                continue;
            }

            if line.starts_with("//IGNORE") {
                ignore = true;
                continue;
            } else if line.starts_with("//CASE ") {
                let case = TestCase {
                    name: name.clone(),
                    content: content.clone(),
                };

                name = String::from(base_name) + "@" + line.strip_prefix("//CASE ").unwrap().trim();
                content.clear();

                if !case.content.is_empty() {
                    return Some(case);
                }
            } else {
                writeln!(content, "{line}").unwrap();
            }
        }

        if !content.is_empty() {
            let case = TestCase {
                name: name.clone(),
                content: content.clone(),
            };
            content.clear();
            Some(case)
        } else {
            None
        }
    });

    base_iter.filter(move |case| case.name.contains(filter))
}

fn file_test<F, E>(
    path: PathBuf,
    success_test: &F,
    err_test: &E,
    filter: &str,
) -> Result<(), String>
where
    F: Fn(SessionKey, TestCase),
    E: Fn(SessionKey, TestCase),
    for<'a> &'a F: UnwindSafe,
    for<'a> &'a E: UnwindSafe,
{
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let content = fs::read_to_string(&path).unwrap();

    let mut panic_cause = Ok(());

    for case in collect_cases_from_file(&name, &content, filter) {
        println!("Running test {name}...");
        if let Err(cause) = std::panic::catch_unwind(|| {
            Session::with_default(|key| {
                if name.starts_with("err_") {
                    err_test(key, case);
                } else {
                    success_test(key, case);
                }
            })
        }) {
            println!("  > {name} FAILED");

            if panic_cause.is_ok() {
                panic_cause = Err(String::new());
            }

            let new_cause = cause.downcast::<String>().ok();
            let panic_cause = panic_cause.as_mut().unwrap_err();

            write!(panic_cause, "  {name}").unwrap();
            if let Some(cause) = new_cause {
                write!(panic_cause, ": {cause}").unwrap();
            }
            writeln!(panic_cause).unwrap();
        } else {
            println!("  > {name} ok");
        }
    }

    panic_cause
}
