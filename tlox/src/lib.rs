//! The Lox treewalking interpreter.

use std::path::PathBuf;

use structopt::StructOpt;

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
