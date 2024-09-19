//! Errors and diagnostics.

use crate::span::{SourceMap, Span};

pub trait Diagnostic {
    fn into_diag(self) -> Diag;
}

#[derive(Debug, Clone)]
pub struct Diag {
    kind: DiagKind,
    message: String,
    primary: DiagLabel,
    secondary: Vec<DiagLabel>,
    notes: Vec<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagKind {
    Warning,
    Error,
}

#[derive(Debug, Clone)]
pub struct DiagLabel {
    span: Span,
    label: String,
}

impl DiagLabel {
    pub fn new(span: Span, label: impl Into<String>) -> Self {
        Self {
            span,
            label: label.into(),
        }
    }
}

impl Diag {
    pub fn new(
        kind: DiagKind,
        message: impl Into<String>,
        primary_span: Span,
        primary_label: impl Into<String>,
    ) -> Self {
        Self {
            kind,
            message: message.into(),
            primary: DiagLabel::new(primary_span, primary_label),
            secondary: Vec::new(),
            notes: Vec::new(),
        }
    }

    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.secondary.push(DiagLabel::new(span, label));
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }
}

#[derive(Debug, Clone)]
pub struct DiagContext {
    pending: Vec<Diag>,
}

impl DiagContext {
    pub fn has_errors(&self) -> bool {
        self.pending.iter().any(|d| d.kind == DiagKind::Error)
    }

    pub fn emit<D: Diagnostic>(&mut self, diag: D) {
        self.pending.push(diag.into_diag());
    }

    pub fn report(&self, source: &SourceMap) {
        todo!()
    }
}
