//! The Lox treewalking interpreter.

#![feature(hash_raw_entry)]
#![feature(concat_idents)]

use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use context::with_new_session;
use diag::{Diag, DiagContext, DiagKind, Diagnostic};
use interp::Interpreter;
use parse::parse_source;
use span::{SourceMap, SourceName};
use structopt::StructOpt;

macro_rules! debug_println {
    (@ $($tt:tt)*) => { };

    ($($tt:tt)*) => {
        #[cfg(debug_assertions)]
        {
            eprintln!($($tt)*);
        }
    };
}

pub mod intern;

mk_internable! {
    expr: syn::Expr,
}

pub mod context;
pub mod diag;
pub mod error;
pub mod interp;
pub mod parse;
pub mod span;
pub mod syn;
pub mod tok;
pub mod ty;
pub mod util;
pub mod val;

/// A Lox tree-walking interpreter
#[derive(Debug, StructOpt)]
pub struct TLox {
    /// script file to run
    pub script: Option<PathBuf>,
}

impl TLox {
    pub fn run() -> ExitCode {
        let Self { script } = Self::from_args();
        with_new_session(move |_| {
            if let Some(path) = script {
                match fs::read_to_string(&path) {
                    Ok(content) => {
                        if Self::run_source(path, &content).is_some() {
                            ExitCode::SUCCESS
                        } else {
                            ExitCode::FAILURE
                        }
                    }

                    Err(io_err) => {
                        FileReadError::from_io(path, io_err).emit();
                        DiagContext::report_current();
                        ExitCode::FAILURE
                    }
                }
            } else {
                let reader = io::stdin();
                let mut buffer = String::new();
                let mut next_input = 0;
                loop {
                    let current_input = next_input;
                    next_input += 1;
                    buffer.clear();

                    print!("> ");
                    io::stdout().flush().unwrap();
                    if let Err(err) = reader.read_line(&mut buffer) {
                        FileReadError::from_io(current_input, err).emit();
                        DiagContext::report_current();
                        continue;
                    }

                    if buffer.trim().is_empty() {
                        break ExitCode::SUCCESS;
                    } else {
                        Self::run_source(current_input, &buffer);
                    }
                }
            }
        })
    }

    fn run_source(name: impl Into<SourceName>, source: &str) -> Option<()> {
        let idx = SourceMap::add_source_to_current(name, source);
        if let Some(res) = parse_source(idx).and_then(|expr| Interpreter {}.eval(&expr)) {
            println!("{res}");
            Some(())
        } else {
            if DiagContext::current_has_errors() {
                DiagContext::report_current();
            }
            None
        }
    }
}

struct FileReadError {
    io_err: io::Error,
    source: SourceName,
}

impl FileReadError {
    fn from_io(source: impl Into<SourceName>, io_err: io::Error) -> Self {
        Self {
            io_err,
            source: source.into(),
        }
    }
}

impl Diagnostic for FileReadError {
    fn into_diag(self) -> Diag {
        Diag::new(
            DiagKind::Error,
            format!("couldn't read input file {}: {}", self.source, self.io_err),
        )
    }
}
