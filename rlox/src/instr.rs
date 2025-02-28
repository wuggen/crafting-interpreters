//! Lox bytecode instructions and encoding.

use std::io;

use crate::chunk::Chunk;

macro_rules! first {
    (($($tt:tt)*) $(, ($($_rest:tt)*))*) => {
        $($tt)*
    };
}

macro_rules! last {
    (($($tt:tt)*)) => {
        $($tt)*
    };

    (($($_first:tt)*) $(, ($($rest:tt)*))*) => {
        last!($(($($rest)*)),*)
    };
}

macro_rules! read_byte {
    ($ip:expr) => {
        unsafe {
            let b = *$ip;
            $ip = ($ip).add(1);
            b
        }
    };
}

macro_rules! init_opds {
    ($ip:expr, $name:ident $(( $($field:ident : $fieldty:ty),* ))?) => {
        {
            init_opds!(@ $ip => $( $($field),* )?);
            Some(Instr::$name $( ($($field),*) )?)
        }
    };

    (@ $ip:expr => $field:ident $(, $($rest:tt)*)?) => {
        let $field = read_byte!($ip);
        init_opds!(@ $ip => $($($rest)*)?);
    };

    (@ $ip:expr => ) => {};
}

macro_rules! define_instrs {
    ($($const:ident $name:ident $(( $($field:ident : $fieldty:ty),* ))? => $mnem:expr),* $(,)?) => {
        /// A Lox instruction opcode.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        #[repr(u8)]
        pub enum Op {
            $($name,)*
        }

        $(
            pub const $const: u8 = Op::$name as u8;
        )*

        const FIRST: Op = first!($((Op::$name)),*);
        const LAST: Op = last!($((Op::$name)),*);

        impl Op {
            /// Get the assembly mnemonic for this opcode.
            pub const fn mnemonic(self) -> &'static str {
                match self {
                    $(Self::$name => $mnem),*
                }
            }
        }

        /// A decoded Lox instruction.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Instr {
            $(
                $name $( ( $($fieldty),* ) )?
            ),*
        }

        impl Instr {
            /// Get the opcode of this instruction.
            pub const fn op(&self) -> Op {
                #[allow(unused_variables)]
                match self {
                    $(
                        Instr::$name $( ($($field),*) )? => Op::$name
                    ),*
                }
            }

            /// Decode an instruction from an IP pointer.
            ///
            /// This function decodes an instruction pointed to by the given IP, and simultaneously shifts
            /// the IP forward by the length of the decoded instruction.
            ///
            /// Returns `None` if the first byte pointed to by the IP is not a valid opcode. In this case,
            /// the IP will still be shifted forwards one byte.
            ///
            /// # Safety
            ///
            /// The IP should point into a valid byte slice. The portion of the slice pointed to should
            /// contain at least one opcode and any operands to that opcode.
            #[inline(always)]
            pub unsafe fn decode_ptr(ip: &mut *const u8) -> Option<Self> {
                match Op::from_byte(read_byte!(*ip))? {
                    $(
                        Op::$name => init_opds!(*ip, $name $(( $($field: $fieldty),* ))?),
                    )*
                }
            }

            pub fn disassemble<W: ::std::io::Write>(
                &self,
                chunk: &$crate::chunk::Chunk,
                offset: usize,
                span: ::std::option::Option<$crate::span::Location>,
                mut stream: W,
            ) -> ::std::io::Result<()> {
                write!(stream, "{offset:04x} ")?;
                if let Some(span) = span {
                    write!(stream, "{span:>8} | ")?;
                } else {
                    write!(stream, "         | ")?;
                }

                #[allow(unused_variables)]
                match self {
                    $(
                        Instr::$name $(( $($field),* ))? => {
                            write!(stream, "{:16} ", self.op().mnemonic())?;
                            $({
                                $(
                                    let $field: ();
                                )*
                                self::disasm_helper(self, chunk, offset, &mut stream)?;
                            })?
                            writeln!(stream)
                        }
                    )*
                }
            }
        }
    };
}

fn disasm_helper<W: io::Write>(
    instr: &Instr,
    chunk: &Chunk,
    _offset: usize,
    mut stream: W,
) -> io::Result<()> {
    match instr {
        &Instr::Const(idx) => {
            write!(
                stream,
                "{idx:02x} ({idx:3}) => {:?}",
                chunk.constants()[idx as usize],
            )
        }
        _ => Ok(()),
    }
}

define_instrs! {
    OP_RET Ret => "ret",
    OP_CONST Const(idx: u8) => "const",
    OP_NEG Neg => "neg",
    OP_ADD Add => "add",
    OP_SUB Sub => "sub",
    OP_MUL Mul => "mul",
    OP_DIV Div => "div",
}

impl Op {
    /// Get this opcode's byte representation.
    #[inline]
    pub const fn to_byte(self) -> u8 {
        self as u8
    }

    /// Decode a byte into an opcode.
    ///
    /// Returns `None` if the byte does not represent any opcode.
    #[inline]
    pub const fn from_byte(byte: u8) -> Option<Self> {
        if byte >= FIRST as u8 && byte <= LAST as u8 {
            Some(unsafe { std::mem::transmute::<u8, Op>(byte) })
        } else {
            None
        }
    }
}

impl Instr {
    /// Get the encoded length of this instruction in bytes.
    pub fn encoded_len(&self) -> usize {
        match self {
            Instr::Const(_) => 2,
            _ => 1,
        }
    }

    /// Decode an instruction.
    ///
    /// This function decodes an instruction from the front of the given byte
    /// slice, and simultaneously shifts the given byte slice forward to the
    /// next instruction in the stream.
    ///
    /// Returns `None` if the first byte in the slice is not a valid opcode. In
    /// this case, the slice will still be shifted forward by one byte.
    ///
    /// # Safety
    ///
    /// The given slice must contain at least one opcode, and any operands to
    /// that opcode. In debug builds, this function will panic if this is not
    /// the case.
    #[inline]
    pub unsafe fn decode(code: &mut &[u8]) -> Option<Self> {
        debug_assert!(!code.is_empty());

        let mut ip = code.as_ptr();
        unsafe {
            let instr = Self::decode_ptr(&mut ip);
            let diff = ip.offset_from_unsigned(code.as_ptr());
            *code = code.split_at_unchecked(diff).1;
            instr
        }
    }
}
