//! Abstract syntax definitions.

use std::fmt::Debug;

use crate::tok::Location;

pub struct SynTree {
    pub node: Box<SynTreeNode>,
    pub location: Location,
}

impl SynTree {
    pub fn binop(location: Location, op: BinopSym, left: SynTree, right: SynTree) -> Self {
        Self {
            node: Box::new(SynTreeNode::Binop { op, left, right }),
            location,
        }
    }

    pub fn unop(location: Location, op: UnopSym, oprd: SynTree) -> Self {
        Self {
            node: Box::new(SynTreeNode::Unop { op, oprd }),
            location,
        }
    }

    pub fn literal(location: Location, val: Literal) -> Self {
        Self {
            node: Box::new(SynTreeNode::Literal { val }),
            location,
        }
    }
}

pub enum SynTreeNode {
    Binop {
        op: BinopSym,
        left: SynTree,
        right: SynTree,
    },

    Unop {
        op: UnopSym,
        oprd: SynTree,
    },

    Literal {
        val: Literal,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinopSym {
    Plus,
    Minus,
    Mul,
    Div,
    Eq,
    NEq,
    Less,
    LessEq,
    Greater,
    GreaterEq,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnopSym {
    Neg,
    Not,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Str(String),
    Num(f64),
    Bool(bool),
    Nil,
}
