//! Runtime Lox values.

use std::cell::{RefCell, RefMut};
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

use crate::builtin::Builtin;
use crate::callable::Callable;
use crate::error::{RuntimeError, RuntimeResult};
use crate::eval::{Env, Interpreter, PlaceVal};
use crate::span::Spanned;
use crate::symbol::Symbol;
use crate::syn::Stmt;
use crate::ty::{PrimitiveTy, Ty};

/// A runtime value.
#[derive(Debug, Clone)]
pub enum Value<'s> {
    Nil,
    Bool(bool),
    Num(f64),
    Str(StrValue<'s>),
    Fun(FunValue<'s>),
    Class(ClassValue<'s>),
    Instance(InstanceValue<'s>),
}

impl<'s> Value<'s> {
    /// Get the type of this value.
    pub fn ty(&self) -> Ty {
        match self {
            Value::Nil => Ty::Primitive(PrimitiveTy::Nil),
            Value::Bool(_) => Ty::Primitive(PrimitiveTy::Bool),
            Value::Num(_) => Ty::Primitive(PrimitiveTy::Num),
            Value::Str(_) => Ty::Primitive(PrimitiveTy::Str),
            Value::Fun(_) => Ty::Primitive(PrimitiveTy::Fun),
            Value::Class(_) => Ty::Primitive(PrimitiveTy::Class),
            Value::Instance(_) => Ty::Primitive(PrimitiveTy::Instance),
        }
    }

    /// Is this value truthy?
    ///
    /// Nil and false are falsey; all other values are truthy.
    pub fn is_truthy(&self) -> bool {
        !matches!(self, Value::Nil | Value::Bool(false))
    }

    /// Get this value as a `Callable`, if it is callable.
    pub fn callable(&self) -> Option<&dyn Callable<'s>> {
        match self {
            Value::Fun(val) => Some(val),
            Value::Class(val) => Some(val),
            _ => None,
        }
    }
}

impl Display for Value<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Num(n) => write!(f, "{n}"),
            Value::Str(s) => write!(f, "{s}"),
            Value::Fun(FunValue::Builtin(b)) => write!(f, "<builtin fun {b}"),
            Value::Fun(FunValue::User(fun)) => write!(f, "<fun {}>", fun.name),
            Value::Class(val) => write!(f, "{}", val.name),
            Value::Instance(val) => write!(f, "<{} instance>", val.class.name),
        }
    }
}

// Note: implementing `PartialEq` between `Value`s of arbitrary lifetimes can potentially cause
// spurious (or is this desired? We let it distinguish between static and computed string
// values 🤔) unequal comparisons between static string values that are logically equal but interned
// in different sessions. This shouldn't be a problem in practice, but hey, putting this note here
// in case I'm wrong about that.
//
// Also, just in case it isn't clear: this is manual instead of derived because the derived
// implementation enforces the _same_ lifetime between operands. There are some tests over in
// eval/test.rs that rely on being able to compare arbitrarily lived `Value`s (though none
// of them compare string values, which is what the lifetime's there for :P)
impl<'s> PartialEq<Value<'s>> for Value<'_> {
    fn eq(&self, other: &Value<'s>) -> bool {
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Bool(b1), Value::Bool(b2)) => b1 == b2,
            (Value::Num(n1), Value::Num(n2)) => n1 == n2,
            (Value::Str(s1), Value::Str(s2)) => s1 == s2,
            _ => false,
        }
    }
}

impl PartialEq<bool> for Value<'_> {
    fn eq(&self, other: &bool) -> bool {
        if let Value::Bool(b) = self {
            b == other
        } else {
            false
        }
    }
}

impl PartialEq<f64> for Value<'_> {
    fn eq(&self, other: &f64) -> bool {
        if let Value::Num(n) = self {
            n == other
        } else {
            false
        }
    }
}

impl PartialEq<&str> for Value<'_> {
    fn eq(&self, other: &&str) -> bool {
        if let Value::Str(s) = self {
            s.as_ref() == *other
        } else {
            false
        }
    }
}

/// A string value.
///
/// A string value can be either static or computed. Static strings are those that are defined
/// directly in the program text as literals, and are interned during lexical analysis. Computed
/// strings are constructed at runtime, are not interned, and are represented by reference-counted
/// Rust `String`s.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StrValue<'s> {
    Static(Symbol<'s>),
    Computed(Rc<String>),
}

impl AsRef<str> for StrValue<'_> {
    fn as_ref(&self) -> &str {
        match self {
            StrValue::Static(s) => s,
            StrValue::Computed(s) => s,
        }
    }
}

impl Display for StrValue<'_> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", <Self as AsRef<str>>::as_ref(self))
    }
}

impl StrValue<'_> {
    /// Concatenate two string values.
    ///
    /// String values in Lox are immutable; concatenation produces a new string value whose
    /// contents are the concatenation of the two operands.
    pub fn concat(&self, other: &Self) -> Self {
        StrValue::Computed(Rc::new(
            [self.as_ref(), other.as_ref()]
                .into_iter()
                .collect::<String>(),
        ))
    }
}

#[derive(Debug, Clone)]
pub enum FunValue<'s> {
    Builtin(Builtin),
    User(Rc<UserFun<'s>>),
}

impl<'s> Callable<'s> for FunValue<'s> {
    fn name(&self) -> Symbol<'s> {
        match self {
            FunValue::Builtin(builtin) => builtin.name(),
            FunValue::User(fun) => fun.name(),
        }
    }

    fn arity(&self) -> u8 {
        match self {
            FunValue::Builtin(builtin) => builtin.arity(),
            FunValue::User(fun) => fun.arity(),
        }
    }

    fn call(
        &self,
        interpreter: &mut Interpreter<'s, '_>,
        args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>> {
        match self {
            FunValue::Builtin(builtin) => builtin.call(interpreter, args),
            FunValue::User(fun) => fun.call(interpreter, args),
        }
    }
}

#[derive(Debug, Clone)]
pub struct UserFun<'s> {
    name: Symbol<'s>,
    args: Vec<Spanned<Symbol<'s>>>,
    code: Vec<Spanned<Stmt<'s>>>,
    env: Env<'s>,
}

impl<'s> UserFun<'s> {
    pub fn new(
        name: Symbol<'s>,
        args: &[Spanned<Symbol<'s>>],
        code: &[Spanned<Stmt<'s>>],
        env: Env<'s>,
    ) -> Self {
        Self {
            name,
            args: Vec::from(args),
            code: Vec::from(code),
            env,
        }
    }
}

impl<'s> Callable<'s> for UserFun<'s> {
    fn name(&self) -> Symbol<'s> {
        self.name
    }

    fn arity(&self) -> u8 {
        self.args.len() as u8
    }

    fn call(
        &self,
        interpreter: &mut Interpreter<'s, '_>,
        args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>> {
        debug_assert_eq!(args.len(), self.args.len());

        let mut env = self.env.clone();
        let _guard = env.push_scope();
        for (name, val) in self.args.iter().copied().zip(args.iter().cloned()) {
            env.declare(name, val);
        }

        interpreter
            .eval_with_env(&mut env, &self.code)
            .or_else(|errs| {
                if let [RuntimeError::FunReturn { val }] = &errs[..] {
                    Ok(val.clone())
                } else {
                    Err(errs)
                }
            })
    }
}

#[derive(Debug, Clone)]
pub struct ClassValue<'s> {
    name: Symbol<'s>,
    methods: Rc<HashMap<Symbol<'s>, Rc<UserFun<'s>>>>,
}

impl<'s> ClassValue<'s> {
    pub fn new(name: Symbol<'s>, methods: HashMap<Symbol<'s>, Rc<UserFun<'s>>>) -> Self {
        let methods = Rc::new(methods);
        Self { name, methods }
    }
}

impl<'s> Callable<'s> for ClassValue<'s> {
    fn name(&self) -> Symbol<'s> {
        self.name
    }

    fn arity(&self) -> u8 {
        0
    }

    fn call(
        &self,
        _interpreter: &mut Interpreter<'s, '_>,
        _args: &[Value<'s>],
    ) -> RuntimeResult<'s, Value<'s>> {
        Ok(Value::Instance(InstanceValue {
            class: self.clone(),
            properties: Rc::new(RefCell::new(HashMap::new())),
        }))
    }
}

#[derive(Debug, Clone)]
pub struct InstanceValue<'s> {
    class: ClassValue<'s>,
    properties: Rc<RefCell<HashMap<Symbol<'s>, Value<'s>>>>,
}

impl<'s> InstanceValue<'s> {
    pub fn get_property(&self, name: Symbol<'s>) -> Option<Value<'s>> {
        self.properties.borrow().get(&name).cloned().or_else(|| {
            self.class
                .methods
                .get(&name)
                .map(|method| Value::Fun(FunValue::User(method.clone())))
        })
    }

    pub fn get_property_place(&self, name: Symbol<'s>) -> PlaceVal<'_, 's> {
        let properties = self.properties.borrow_mut();
        let val = RefMut::map(properties, |props| props.entry(name).or_insert(Value::Nil));
        PlaceVal::new(val)
    }
}
