//! Built-in Lox functions

use std::fmt::{self, Display, Formatter};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::callable::Callable;
use crate::error::RuntimeResult;
use crate::eval::{Env, Interpreter};
use crate::symbol::static_syms::SYM_CLOCK;
use crate::symbol::Symbol;
use crate::val::{CallableValue, Value};

#[derive(Debug, Clone)]
pub enum Builtin {
    Clock,
}

impl Builtin {
    pub fn sym(&self) -> Symbol<'static> {
        match self {
            Builtin::Clock => SYM_CLOCK,
        }
    }

    pub fn declare_builtins(env: &mut Env<'_>) {
        env.declare(
            SYM_CLOCK,
            Value::Callable(CallableValue::Builtin(Builtin::Clock)),
        );
    }
}

impl Display for Builtin {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.sym())
    }
}

impl<'s> Callable<'s> for Builtin {
    fn name(&self) -> Symbol<'s> {
        self.sym()
    }

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
