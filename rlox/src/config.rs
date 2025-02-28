//! Compile-time interpreter configuration.

pub const VM_TRACE: bool = option_env!("RLOX_VM_TRACE").is_some();
