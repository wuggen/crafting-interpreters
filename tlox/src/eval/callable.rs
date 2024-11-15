//! Lox user and built-in function evaluation.

use std::time::{SystemTime, UNIX_EPOCH};

use super::Interpreter;
use crate::error::RuntimeResult;
use crate::val::Value;

pub trait Callable<'s> {
    fn arity(&self) -> usize;

    fn call(
        &self,
        interpreter: &mut Interpreter<'s, '_>,
        args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    Clock,
}

impl<'s> Callable<'s> for Builtin {
    fn arity(&self) -> usize {
        match self {
            Builtin::Clock => 0,
        }
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter<'s, '_>,
        _args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>> {
        debug_assert!(_args.is_empty());

        match self {
            Builtin::Clock => {
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs_f64();
                Ok(Value::Num(now))
            }
        }
    }
}
