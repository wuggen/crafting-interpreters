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

        #[allow(clippy::single_match)] // This match will expand quickly lol
        match instr {
            Instr::Const(idx) => self.code.push(idx),
            _ => {}
        }

        let len = instr.encoded_len();

        if self.spans.is_empty() || span != self.spans.last().unwrap().0 {
            self.spans.push((span, len));
        } else {
            self.spans.last_mut().unwrap().1 += len;
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
            let span = self
                .span_at_offset(offset)
                .expect("span not found for offset");

            let given_span = if Some(span) == prev_span {
                None
            } else {
                Some(span)
            };
            prev_span = Some(span);

            let instr = unsafe { Instr::decode(&mut code) };
            if let Some(instr) = instr {
                instr.disassemble(self, offset, given_span, &mut stream)?;
                offset += instr.encoded_len();
            } else {
                writeln!(stream, "Unknown opcode {:02x}", self.code[offset])?;
                offset += 1;
            }
        }

        Ok(())
    }

    /// Get the bytecode of this chunk.
    pub fn code(&self) -> &[u8] {
        &self.code
    }

    /// Get the constant pool of this chunk.
    pub fn constants(&self) -> &[Value] {
        &self.constants
    }

    /// Get the byte offset of a pointer into this chunk's code.
    ///
    /// If the given pointer is outside of this chunk's allocation, returns `None`.
    pub fn offset_of_ptr(&self, ptr: *const u8) -> Option<usize> {
        let code_ptr = self.code.as_ptr();
        let diff = ptr as isize - code_ptr as isize;
        if diff < 0 || diff > self.code.len() as isize {
            None
        } else {
            Some(diff as usize)
        }
    }

    pub fn code_from_ptr(&self, ptr: *const u8) -> Option<&[u8]> {
        let offset = self.offset_of_ptr(ptr)?;
        Some(&self.code[offset..])
    }

    /// Get the source code span corresponding to the given byte offset in this chunk's code.
    pub fn span_at_offset(&self, offset: usize) -> Option<Location> {
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

    #[inline]
    pub unsafe fn constant_unchecked(&self, idx: u8) -> Value {
        unsafe {
            *self.constants.get_unchecked(idx as usize)
        }
    }
}
