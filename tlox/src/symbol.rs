//! Symbols, i.e. interned strings.

use std::borrow::Borrow;
use std::collections::HashSet;
use std::hash::Hash;
use std::ops::Deref;
use std::ptr;
use std::sync::Mutex;

use crate::arena::DroplessArena;
use crate::session::SessionKey;
use crate::util::with_lifetime;

#[derive(Default)]
pub struct SymbolInterner {
    arena: DroplessArena,
    syms: Mutex<HashSet<&'static str>>,
}

impl SymbolInterner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_key<'s>(&'s self, _: SessionKey<'s>) -> UnlockedSymbolInterner<'s> {
        UnlockedSymbolInterner { interner: self }
    }
}

pub struct UnlockedSymbolInterner<'s> {
    interner: &'s SymbolInterner,
}

impl<'s> UnlockedSymbolInterner<'s> {
    pub fn intern(&self, val: &str) -> Symbol<'s> {
        let mut syms = self.interner.syms.lock().unwrap();
        if let Some(interned) = syms.get(val) {
            unsafe { Symbol(with_lifetime(interned)) }
        } else {
            let interned_ref = self.interner.arena.alloc_str(val);
            syms.insert(unsafe { with_lifetime(interned_ref) });
            Symbol(interned_ref)
        }
    }
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord)]
pub struct Symbol<'s>(&'s str);

impl PartialEq for Symbol<'_> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl Eq for Symbol<'_> {}

impl Deref for Symbol<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl Borrow<str> for Symbol<'_> {
    fn borrow(&self) -> &str {
        self
    }
}

impl Hash for Symbol<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        ptr::hash(self.0, state);
    }
}

impl Symbol<'_> {
    pub fn intern<'s>(key: SessionKey<'s>, val: &str) -> Symbol<'s> {
        key.get().syms.with_key(key).intern(val)
    }

    pub fn as_str(&self) -> &str {
        self.0
    }
}

#[macro_export]
macro_rules! sym {
    ($key:expr, $s:expr) => {
        Symbol::intern($key, $s)
    };
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::session::Session;

    #[test]
    fn pointer_equality() {
        Session::with_default(|key| {
            let a_string = String::from("lol hey");
            let b_string = String::from("lol hey");

            let a = sym!(key, &a_string);
            let b = sym!(key, &b_string);

            eprintln!("a ptr {:p}, b ptr {:p}", a.0, b.0);

            assert_eq!(a, b);
            assert!(ptr::eq(a.0, b.0));
        });
    }
}