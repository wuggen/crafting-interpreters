//! The Lox treewalking interpreter.

use std::path::PathBuf;

use structopt::StructOpt;

pub mod parse;
pub mod span;
pub mod syn;
pub mod tok;

#[derive(Debug, StructOpt)]
pub struct TLox {
    pub script: Option<PathBuf>,
}
