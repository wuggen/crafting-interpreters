//! Global interpreter context.
//!
//! This includes such things as the source map, diagnostic context, syntax trees, and interned
//! strings and identifiers. It is stored globally for each interpreter instance, and accessible by
//! any code in the interpreter's context.

use std::cell::RefCell;
use std::sync::{Arc, RwLock, Weak};

use crate::diag::DiagContext;
use crate::span::SourceMap;

thread_local! {
    static CONTEXT: RefCell<Weak<Context>> = const { RefCell::new(Weak::new()) };
}

/// An interpreter instance.
#[derive(Debug, Default)]
pub struct Interpreter {
    context: Arc<Context>,
}

impl Interpreter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Enter this interpreter's context on the current thread.
    ///
    /// # Panics
    ///
    /// This method will panic if the current thread is already in the context of some interpreter,
    /// including this one.
    pub fn enter(&self) {
        CONTEXT.with_borrow_mut(|cx| {
            if cx.upgrade().is_some() {
                panic!("cannot enter; thread is already in an interpreter context");
            }

            *cx = Arc::downgrade(&self.context);
        });
    }

    /// Exit this interpreter's context on the current thread.
    ///
    /// # Panics
    ///
    /// This method will panic if the current thread is not in this interpreter's context. This can
    /// happen if the thread is in a different interpreter's context, or if it is under no
    /// interpreter's context at all.
    pub fn exit(&self) {
        CONTEXT.with_borrow_mut(|cx| {
            if cx.as_ptr() != Arc::as_ptr(&self.context) {
                panic!("cannot exit; thread is not in this interpreter's context");
            }

            *cx = Weak::new();
        });
    }

    /// Is the current thread in the context of this interpreter?
    ///
    /// This method will only return true if the calling thread is in the context of _this
    /// particular_ interpeter instance. To check whether the current thread is in the context of
    /// _any_ interpreter, use the non-method [`in_context`] function.
    pub fn in_context(&self) -> bool {
        CONTEXT.with_borrow(|cx| cx.as_ptr() == Arc::as_ptr(&self.context))
    }
}

/// Global interpreter context.
///
/// Each context belongs to a particular interpreter instance. A thread may
/// [`enter`](Interpreter::enter) the context of an interpreter to make that interpreter's
/// `Context` available to all code running on that thread, via [`with_context`]. A thread may be
/// in the context of no more than one interpreter at a time. #[derive(Debug)]
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

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_source_map<T>(&self, f: impl FnOnce(&SourceMap) -> T) -> T {
        f(&self.source_map.read().unwrap())
    }

    pub fn with_source_map_mut<T>(&self, f: impl FnOnce(&mut SourceMap) -> T) -> T {
        f(&mut self.source_map.write().unwrap())
    }

    pub fn with_diag_context<T>(&self, f: impl FnOnce(&DiagContext) -> T) -> T {
        f(&self.diag_context)
    }
}

/// Perform an action with the global interpreter context.
///
/// This function will panic if called from a thread that is not in the context of an
/// [`Interpreter`].
pub fn with_context<T>(f: impl FnOnce(&Context) -> T) -> T {
    CONTEXT.with_borrow(|cx| {
        let cx = cx
            .upgrade()
            .expect("thread is not in an interpreter context");
        f(&cx)
    })
}

/// Perform an action in the context of a new [`Interpreter`].
///
/// This will create a new [`Interpreter`], enter its context, and execute the given closure. When
/// the closure returns, the [`Interpreter`] will be dropped, and any threads in its context will
/// no longer be so.
pub fn with_new_interpreter<T>(f: impl FnOnce(&Interpreter) -> T) -> T {
    let interpreter = Interpreter::new();
    interpreter.enter();

    f(&interpreter)
}

/// Is the current thread in the context of an interpreter?
pub fn in_context() -> bool {
    CONTEXT.with_borrow(|cx| cx.upgrade().is_some())
}
