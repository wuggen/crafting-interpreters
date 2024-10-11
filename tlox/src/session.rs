//! Global interpreter context.

use crate::diag::DiagContext;
use crate::scoped_thread_local;
use crate::span::SourceMap;

scoped_thread_local!(static SESSION: Session);

/// Global context for an interpreter session.
#[derive(Debug, Default)]
pub struct Session {
    pub dcx: DiagContext,
    pub sm: SourceMap,
}

impl Session {
    /// Do something in the context of this session.
    ///
    /// Until the given closure returns, this session will be accessible in the current thread via
    /// [`Session::with_current`]. Once the closure returns, the previous global session, if any,
    /// becomes current again for the thread.
    pub fn with<T>(&self, f: impl FnOnce(&Session) -> T) -> T {
        SESSION.set(self, || Self::with_current(f))
    }

    /// Do something with the current session.
    ///
    /// Panics if there is no current session in the current thread.
    pub fn with_current<T>(f: impl FnOnce(&Session) -> T) -> T {
        SESSION.with(f)
    }

    /// Does the current thread have a global session?
    pub fn has_current() -> bool {
        SESSION.is_set()
    }

    /// Is this session the current global one for the current thread?
    pub fn is_current(&self) -> bool {
        Self::has_current() && Self::with_current(|s| std::ptr::eq(self, s))
    }

    /// Do something with a new, fresh session.
    ///
    /// Until the given closure returns, the newly-created session will be accessible in the current
    /// thread via [`Session::with_current`]. Once the closure returns, the previous global session,
    /// if any, becomes current again for the thread.
    pub fn with_default<T>(f: impl FnOnce(&Session) -> T) -> T {
        Self::default().with(f)
    }
}
