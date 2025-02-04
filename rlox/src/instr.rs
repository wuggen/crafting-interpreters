//! Lox bytecode instructions and encoding.

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

macro_rules! define_intrs {
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
        }
    };
}

define_intrs! {
    OP_RETURN Return => "return",
    OP_CONST Const(idx: u8) => "const",
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

        let get = |idx: usize| unsafe { *code.get_unchecked(idx) };

        let (res, shift) = match get(0) {
            OP_RETURN => (Some(Instr::Return), 1),
            OP_CONST => {
                debug_assert!(code.len() >= 2);
                (Some(Instr::Const(get(1))), 2)
            }
            _ => (None, 1),
        };

        let (_, tail) = unsafe { code.split_at_unchecked(shift) };
        *code = tail;
        res
    }
}
