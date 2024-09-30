//! Global interpreter context.
//!
//! This includes such things as the source map, and diagnostic context. It is stored globally for
//! each interpreter session, and accessible by any code in the session's context.

use std::cell::RefCell;
use std::sync::{Arc, RwLock, Weak};

use crate::diag::DiagContext;
use crate::span::SourceMap;

thread_local! {
    static CONTEXT: RefCell<Weak<Context>> = const { RefCell::new(Weak::new()) };
}

/// An interpreter session.
#[derive(Debug, Default)]
pub struct Session {
    context: Arc<Context>,
}

impl Session {
    pub fn new() -> Self {
        Self::default()
    }

    /// Enter this session's context on the current thread.
    ///
    /// # Panics
    ///
    /// This method will panic if the current thread is already in the context of some session,
    /// including this one.
    pub fn enter(&self) {
        CONTEXT.with_borrow_mut(|cx| {
            if cx.upgrade().is_some() {
                panic!("cannot enter; thread is already in an session context");
            }

            *cx = Arc::downgrade(&self.context);
        });
    }

    /// Exit this session's context on the current thread.
    ///
    /// # Panics
    ///
    /// This method will panic if the current thread is not in this session's context. This can
    /// happen if the thread is in a different session's context, or if it is under no
    /// session's context at all.
    pub fn exit(&self) {
        CONTEXT.with_borrow_mut(|cx| {
            if cx.as_ptr() != Arc::as_ptr(&self.context) {
                panic!("cannot exit; thread is not in this session's context");
            }

            *cx = Weak::new();
        });
    }

    /// Is the current thread in the context of this session?
    ///
    /// This method will only return true if the calling thread is in the context of _this
    /// particular_ session. To check whether the current thread is in the context of _any_
    /// session, use the non-method [`in_context`] function.
    pub fn in_context(&self) -> bool {
        CONTEXT.with_borrow(|cx| cx.as_ptr() == Arc::as_ptr(&self.context))
    }
}

/// Global interpreter context.
///
/// Each context belongs to a particular interpreter session. A thread may
/// [`enter`](Session::enter) the context of a session to make that session's `Context` available
/// to all code running on that thread, via [`with_context`]. A thread may be in the context of no
/// more than one session at a time. #[derive(Debug)]
#[derive(Debug)]
pub struct Context {
    source_map: RwLock<SourceMap>,
    diag_context: DiagContext,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            source_map: RwLock::new(SourceMap::new()),
            diag_context: DiagContext::new(),
        }
    }
}

macro_rules! accessor {
    (rw $name:ident => $field:ident : $ty:ty) => {
        pub fn $name<T>(&self, f: impl FnOnce(&$ty) -> T) -> T {
            f(&self.$field.read().unwrap())
        }
    };

    (mut rw $name:ident => $field:ident : $ty:ty) => {
        pub fn $name<T>(&self, f: impl FnOnce(&mut $ty) -> T) -> T {
            f(&mut self.$field.write().unwrap())
        }
    };

    ($name:ident => $field:ident : $ty:ty) => {
        pub fn $name<T>(&self, f: impl FnOnce(&$ty) -> T) -> T {
            f(&self.$field)
        }
    };
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    accessor!(rw with_source_map => source_map: SourceMap);
    accessor!(mut rw with_source_map_mut => source_map: SourceMap);
    accessor!(with_diag_context => diag_context: DiagContext);
}

/// Perform an action with the global session context.
///
/// This function will panic if called from a thread that is not in the context of a [`Session`].
pub fn with_context<T>(f: impl FnOnce(&Context) -> T) -> T {
    CONTEXT.with_borrow(|cx| {
        let cx = cx.upgrade().expect("thread is not in an session context");
        f(&cx)
    })
}

/// Perform an action in the context of a new [`Session`].
///
/// This will create a new [`Session`], enter its context, and execute the given closure. When the
/// closure returns, the [`Session`] will be dropped, and any threads in its context will no longer
/// be so.
pub fn with_new_session<T>(f: impl FnOnce(&Session) -> T) -> T {
    let session = Session::new();
    session.enter();

    f(&session)
}

/// Is the current thread in the context of an session?
pub fn in_context() -> bool {
    CONTEXT.with_borrow(|cx| cx.upgrade().is_some())
}
