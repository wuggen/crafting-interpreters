//! The Lox treewalking interpreter.

#![feature(hash_raw_entry)]
#![feature(mapped_lock_guards)]
#![feature(round_char_boundary)]

use std::{
    fs,
    io::{self, Write},
    path::PathBuf,
    process::ExitCode,
};

use diag::{Diag, DiagKind, Diagnostic};
use interp::Interpreter;
use parse::parse_source;
use session::Session;
use span::SourceName;
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
pub mod util;

mk_internable! {
    expr: syn::Expr,
}

pub mod diag;
pub mod error;
pub mod interp;
pub mod parse;
pub mod session;
pub mod span;
pub mod syn;
pub mod tok;
pub mod ty;
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
        Session::with_default(|sess| {
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
                        sess.dcx.report();
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
                        sess.dcx.report();
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
        Session::with_current(|sess| {
            let idx = sess.sm.add_source(name, source);
            if let Some(res) = parse_source(idx).and_then(|expr| Interpreter {}.eval(&expr)) {
                println!("{res}");
                Some(())
            } else {
                if sess.dcx.has_errors() {
                    sess.dcx.report();
                }
                None
            }
        })
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
