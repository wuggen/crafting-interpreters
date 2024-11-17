//! Built-in Lox functions

use std::fmt::{self, Display, Formatter};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::callable::Callable;
use crate::error::RuntimeResult;
use crate::eval::Interpreter;
use crate::val::Value;

#[derive(Debug, Clone)]
pub enum Builtin {
    Clock,
}

impl Display for Builtin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Self::Clock => write!(f, "clock"),
        }
    }
}

impl<'s> Callable<'s> for Builtin {
    fn arity(&self) -> u8 {
        match self {
            Self::Clock => 0,
        }
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter<'s, '_>,
        args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>> {
        debug_assert_eq!(args.len(), self.arity() as usize);

        match self {
            Self::Clock => Ok(Value::Num(
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs_f64(),
            )),
        }
    }
}
