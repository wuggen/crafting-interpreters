//! Bytecode chunks.

use std::io;

use crate::instr::Instr;
use crate::span::Location;
use crate::value::Value;

/// A Lox bytecode chunk.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Chunk {
    code: Vec<u8>,
    constants: Vec<Value>,
    spans: Vec<(Location, usize)>,
}

impl Chunk {
    /// Create a new, empty chunk.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append an instruction to this chunk.
    pub fn write_instr(&mut self, instr: Instr, span: Location) {
        self.code.push(instr.op() as u8);
        match instr {
            Instr::Const(idx) => self.code.push(idx),
            _ => {}
        }

        let len = instr.encoded_len();

        if self.spans.is_empty() {
            self.spans.push((span, len));
        } else {
            if span == self.spans.last().unwrap().0 {
                self.spans.last_mut().unwrap().1 += len;
            } else {
                self.spans.push((span, len));
            }
        }
    }

    /// Append a constant to this chunk's constant pool.
    ///
    /// Returns the index of the added constant, for use in `const` instructions.
    pub fn add_constant(&mut self, value: Value) -> u8 {
        debug_assert!(self.constants.len() < u8::MAX as usize);
        let idx = self.constants.len() as u8;
        self.constants.push(value);
        idx
    }

    /// Dump a disassembly of this chunk and its constant pool to the given output stream.
    pub fn disassemble<W: io::Write>(&self, name: &str, mut stream: W) -> io::Result<()> {
        writeln!(stream, "== {name} ==")?;

        let mut code = self.code.as_slice();
        let mut offset = 0usize;
        let mut prev_span = None;

        while !code.is_empty() {
            write!(stream, "{offset:04x} ")?;
            let span = self.span_at_offset(offset).expect("span not found for offset");
            if Some(span) == prev_span {
                write!(stream, "         | ")?;
            } else {
                write!(stream, "{span:>8} | ")?;
            }
            prev_span = Some(span);
            
            let instr = unsafe { Instr::decode(&mut code) };

            if let Some(instr) = instr {
                match instr {
                    Instr::Return => writeln!(stream, "{}", instr.op().mnemonic())?,
                    Instr::Const(idx) => writeln!(
                        stream,
                        "{:16} {idx:02x} ({idx:3}) => {:?}",
                        instr.op().mnemonic(),
                        self.constants[idx as usize]
                    )?,
                }

                offset += instr.encoded_len();
            } else {
                writeln!(stream, "Unknown opcode {:02x}", self.code[offset])?;
                offset += 1;
            }
        }

        Ok(())
    }
}

impl Chunk {
    fn span_at_offset(&self, offset: usize) -> Option<Location> {
        self.spans
            .iter()
            .scan(
                (Location::default(), 0),
                |(cur_span, cur_offs), (new_span, run_len)| {
                    if *cur_offs > offset {
                        None
                    } else {
                        *cur_span = *new_span;
                        *cur_offs += *run_len;
                        Some(*cur_span)
                    }
                },
            )
            .last()
    }
}
