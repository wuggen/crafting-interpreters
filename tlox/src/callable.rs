use crate::error::RuntimeResult;
use crate::eval::Interpreter;
use crate::symbol::Symbol;
use crate::val::Value;

pub trait Callable<'s> {
    fn name(&self) -> Symbol<'s>;
    fn arity(&self) -> u8;
    fn call(
        &self,
        interpreter: &mut Interpreter<'s, '_>,
        args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>>;
}
