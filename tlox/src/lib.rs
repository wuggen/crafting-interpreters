//! The Lox treewalking interpreter.

use std::path::PathBuf;

use structopt::StructOpt;

pub mod span;
pub mod tok;

#[derive(Debug, StructOpt)]
pub struct TLox {
    pub script: Option<PathBuf>,
}
