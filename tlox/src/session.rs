use crate::{diag::DiagContext, scoped_thread_local, span::SourceMap};

scoped_thread_local!(static SESSION: Session);

#[derive(Debug, Default)]
pub struct Session {
    pub dcx: DiagContext,
    pub sm: SourceMap,
}

impl Session {
    pub fn with<T>(&self, f: impl FnOnce(&Session) -> T) -> T {
        SESSION.set(self, || Self::with_current(f))
    }

    pub fn with_current<T>(f: impl FnOnce(&Session) -> T) -> T {
        SESSION.with(f)
    }

    pub fn has_current() -> bool {
        SESSION.is_set()
    }

    pub fn is_current(&self) -> bool {
        Self::has_current() && Self::with_current(|s| std::ptr::eq(self, s))
    }

    pub fn with_default<T>(f: impl FnOnce(&Session) -> T) -> T {
        Self::default().with(f)
    }
}
