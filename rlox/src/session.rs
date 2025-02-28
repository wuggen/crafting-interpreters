//! rlox interpreter sessions.

use crate::vm::Vm;

#[derive(Debug, Clone)]
pub struct Session {
    pub vm: Vm,
}

impl Session {
    pub fn new() -> Self {
        Self {
            vm: Vm::new(),
        }
    }
}
