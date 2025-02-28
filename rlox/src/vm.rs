//! Lox virtual machine.

use std::io;
use std::ops::{Add, Div, Mul, Sub};

use crate::chunk::Chunk;
use crate::config;
use crate::instr::*;
use crate::value::Value;

#[derive(Debug, Clone)]
pub struct Vm {
    stack: Vec<Value>,
}

const STACK_INIT: usize = 256;

impl Vm {
    pub fn new() -> Self {
        Vm {
            stack: Vec::with_capacity(STACK_INIT),
        }
    }
}

macro_rules! impl_arith_instr {
    ($self:ident, $op:ident) => {{
        debug_assert!($self.stack.len() >= 2);
        let rhs = $self.stack.pop().unwrap();
        let lhs = $self.stack.last_mut().unwrap();
        *lhs = lhs.$op(rhs);
    }};
}

impl Vm {
    pub fn evaluate(&mut self, chunk: &Chunk) -> Result<(), VmError> {
        let mut ip = chunk.code().as_ptr();
        loop {
            let offset = if config::VM_TRACE {
                chunk.offset_of_ptr(ip).unwrap()
            } else {
                0
            };

            let instr = unsafe { Instr::decode_ptr(&mut ip) };

            if config::VM_TRACE {
                eprintln!("{:.3?}", self.stack);
                if let Some(instr) = instr {
                    let span = chunk.span_at_offset(offset);
                    instr
                        .disassemble(chunk, offset, span, io::stderr())
                        .unwrap();
                } else {
                    eprintln!("{offset:04x}          | INVAL");
                }
            }

            match instr {
                Some(Instr::Ret) => {
                    let val = self.stack.pop().ok_or(VmError)?;
                    println!("{val}");
                    return Ok(());
                }
                Some(Instr::Const(idx)) => {
                    debug_assert!(idx as usize <= chunk.constants().len());
                    let val = unsafe { chunk.constant_unchecked(idx) };
                    self.stack.push(val);
                }
                Some(Instr::Neg) => {
                    let val = self.stack.last_mut().ok_or(VmError)?;
                    *val = -*val;
                }
                Some(Instr::Add) => impl_arith_instr!(self, add),
                Some(Instr::Sub) => impl_arith_instr!(self, sub),
                Some(Instr::Mul) => impl_arith_instr!(self, mul),
                Some(Instr::Div) => impl_arith_instr!(self, div),
                None => return Err(VmError),
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("Runtime error during code evaluation")]
pub struct VmError;
