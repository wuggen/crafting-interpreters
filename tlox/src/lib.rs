//! The Lox treewalking interpreter.

use std::path::PathBuf;

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

pub mod context;
pub mod diag;
pub mod parse;
pub mod span;
pub mod syn;
pub mod tok;

/// A Lox tree-walking interpreter
#[derive(Debug, StructOpt)]
pub struct TLox {
    /// script file to run
    pub script: Option<PathBuf>,
}
