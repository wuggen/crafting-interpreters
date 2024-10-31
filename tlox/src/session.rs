//! Global interpreter context.

use std::marker::PhantomData;

use crate::diag::DiagContext;
use crate::scoped_thread_local;
use crate::span::SourceMap;
use crate::symbol::SymbolInterner;

scoped_thread_local!(static SESSION: Session);

/// Global context for an interpreter session.
#[derive(Default)]
pub struct Session {
    pub dcx: DiagContext,
    pub sm: SourceMap,
    pub syms: SymbolInterner,
}

/// A token allowing access to, and carrying the lifetime of, a global `Session`.
///
/// `SessionKey`s are used in [`Session::with`], [`Session::with_current`], and
/// [`Session::with_default`] to denote the lifetime for which a given `Session` is global to a
/// thread. Unlike a reference, it is zero-sized.
///
/// Many interfaces elsewhere in the interpreter take session keys as arguments, to allow data to be
/// borrowed from the current session.
#[derive(Debug, Clone, Copy)]
pub struct SessionKey<'s>(
    PhantomData<&'s mut Session>, /* mutable for invariance */
);

impl SessionKey<'_> {
    /// Construct a new `SessionKey`.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the lifetime attached to the returned key is arbitrary.
    /// Session keys allow borrowing data from the current thread-global session, which does not
    /// live for the `'static` lifetime; hence, the chosen lifetime must not outlive the
    /// currently-global session.
    ///
    /// As a rule of thumb, it is generally safe to create a new session key with a lifetime
    /// derived from a previous session key.
    #[inline(always)]
    pub unsafe fn new<'s>() -> SessionKey<'s> {
        SessionKey(PhantomData)
    }

    /// Construct a `SessionKey` bound to the lifetime of the given reference.
    ///
    /// # Safety
    ///
    /// This function is unsafe for the same reasons, and has the same safety requirements as,
    /// [`SessionKey::new`]; see that function's documentation for details.
    #[inline(always)]
    pub unsafe fn with_lifetime<T>(_: &T) -> SessionKey {
        Self::new()
    }
}

impl<'s> SessionKey<'s> {
    pub fn get(&self) -> &'s Session {
        debug_assert!(SESSION.is_set());
        // Safety: SessionKey is only constructed in the various Session::with_* methods, with a
        // lifetime tied to an object local to those methods. A reference constructed with that
        // lifetime cannot safely escape the closure
        unsafe { &*SESSION.with(|sess| sess as *const _) }
    }
}

impl Session {
    /// Do something in the context of this session.
    ///
    /// Until the given closure returns, this session will be accessible in the current thread via
    /// [`Session::with_current`].
    ///
    /// # Panics
    ///
    /// Panics if there is already a current session for the current thread.
    pub fn with<T>(&self, f: impl FnOnce(SessionKey) -> T) -> T {
        assert!(
            !SESSION.is_set(),
            "already a current session; use `Session::replace_current` instead"
        );
        let key = unsafe { SessionKey::with_lifetime(&self) };
        SESSION.set(self, || f(key))
    }

    /// Do something with the current session.
    ///
    /// # Panics
    ///
    /// Panics if there is no current session in the current thread.
    pub fn with_current<T>(f: impl FnOnce(SessionKey) -> T) -> T {
        // I think technically we'd be fine just using a key with an unbounded lifetime. I don't
        // think rustc does enough global analysis to grow the lifetime beyond what would be
        // safe, it'd just assume that the closure takes borrowed data as an argument and
        // not allow it to escape.
        //
        // But just in case...
        let lifetime = ();
        let key = unsafe { SessionKey::with_lifetime(&lifetime) };
        SESSION.with(|_| f(key))
    }

    /// Does the current thread have a global session?
    pub fn has_current() -> bool {
        SESSION.is_set()
    }

    /// Is this session the current global one for the current thread?
    pub fn is_current(&self) -> bool {
        Self::has_current() && Self::with_current(|key| std::ptr::eq(self, key.get()))
    }

    /// Do something with a new, fresh session.
    ///
    /// Until the given closure returns, the newly-created session will be accessible in the current
    /// thread via [`Session::with_current`]. Once the given closure returns, the session will be
    /// dropped before this function returns.
    ///
    /// # Panics
    ///
    /// Panics if there is already a current session for the current thread.
    pub fn with_default<T>(f: impl FnOnce(SessionKey) -> T) -> T {
        Self::default().with(f)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::sym;

    #[test]
    #[should_panic]
    fn escape() {
        Session::with_default(|key1| {
            let sym = Session::with_default(|_| sym!(key1, "lol"));

            println!("{sym}");
        })
    }
}
