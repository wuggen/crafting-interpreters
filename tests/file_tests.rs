use std::any::Any;
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
        let paths = collect_files(&self.base_path, self.filter_var).collect::<Vec<_>>();

        let mut snap_path = self.base_path.clone();
        snap_path.push("snapshots");

        insta::with_settings!({
            snapshot_path => snap_path,
        }, {
            for path in paths {
                file_test(path, &self.test_fn, &self.err_test_fn);
            }
        });
    }
}

pub fn collect_files(base_path: &Path, filter_var: &str) -> impl Iterator<Item = PathBuf> {
    let filter = std::env::var(filter_var);

    let filter_fn = move |entry: DirEntry| {
        if !entry.file_type().unwrap().is_file() {
            return None;
        }

        if let Ok(filter) = &filter {
            if !entry.path().to_str().unwrap().contains(filter.as_str()) {
                return None;
            }
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
        .inspect(|path| eprintln!("collected test {}", path.display()))
}

pub fn collect_cases_from_file<'a>(
    base_name: &'a str,
    file_content: &'a str,
) -> impl Iterator<Item = TestCase> + use<'a> {
    let mut name = String::from(base_name);
    let mut content = String::new();
    let mut lines = file_content.lines();
    std::iter::from_fn(move || {
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
    })
}

fn file_test<F, E>(path: PathBuf, success_test: &F, err_test: &E)
where
    F: Fn(SessionKey, TestCase),
    E: Fn(SessionKey, TestCase),
    for<'a> &'a F: UnwindSafe,
    for<'a> &'a E: UnwindSafe,
{
    eprintln!("file test for {}", path.display());
    let name = path.file_name().unwrap().to_string_lossy().into_owned();
    let content = fs::read_to_string(&path).unwrap();

    let mut panic_cause: Option<Box<dyn Any + Send>> = None;

    for case in collect_cases_from_file(&name, &content) {
        if let Err(cause) = std::panic::catch_unwind(|| {
            Session::with_default(|key| {
                if name.starts_with("err_") {
                    eprintln!(" => err test");
                    err_test(key, case);
                } else {
                    eprintln!(" => success test");
                    success_test(key, case);
                }
            })
        }) {
            panic_cause = Some(cause);
        }
    }

    if let Some(cause) = panic_cause {
        std::panic::resume_unwind(cause);
    }
}
