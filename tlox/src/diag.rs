//! Errors and diagnostics.

use std::sync::Mutex;

use crate::session::Session;
use crate::span::Span;

/// Warning and error types.
pub trait Diagnostic: Sized {
    /// Create a [`Diag`] from `self`.
    ///
    /// [`Diag`] is the unified diagnostic type that is ultimately used to report diagnostic
    /// messages to the user.
    fn into_diag(self) -> Diag;

    /// Emit this diagnostic to the global context.
    ///
    /// This method will panic if called from a thread that is not currently in the context of an
    /// [`Session`].
    fn emit(self) {
        Session::with_current(|key| {
            key.get().dcx.emit(self);
        })
    }
}

/// A diagnostic message.
///
/// Diagnostics contain a message, a primary span and label, optional secondary spans and labels,
/// and optional notes.
#[derive(Debug, Clone)]
pub struct Diag {
    kind: DiagKind,
    message: String,
    labels: Vec<DiagLabel>,
    notes: Vec<String>,
}

/// Diagnostic kind; warning or error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagKind {
    Warning,
    Error,
}

/// Diagnostic label kind; primary or secondary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LabelKind {
    Primary,
    Secondary,
}

/// A label on a [`Span`].
#[derive(Debug, Clone)]
pub struct DiagLabel {
    kind: LabelKind,
    span: Span,
    label: String,
}

impl DiagLabel {
    /// Create a new diagnostic label.
    pub fn new(kind: LabelKind, span: Span, label: impl Into<String>) -> Self {
        Self {
            kind,
            span,
            label: label.into(),
        }
    }

    /// Create a primary diagnostic label.
    pub fn primary(span: Span, label: impl Into<String>) -> Self {
        Self::new(LabelKind::Primary, span, label)
    }

    /// Create a secondary diagnostic label.
    pub fn secondary(span: Span, label: impl Into<String>) -> Self {
        Self::new(LabelKind::Secondary, span, label)
    }
}

impl Diagnostic for Diag {
    fn into_diag(self) -> Diag {
        self
    }
}

impl Diag {
    /// Create a new diagnostic.
    pub fn new(kind: DiagKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
            labels: Vec::new(),
            notes: Vec::new(),
        }
    }

    /// Builder method that adds a primary label to the diagnostic.
    pub fn with_primary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.labels.push(DiagLabel::primary(span, label));
        self
    }

    /// Builder method that adds a secondary label to the diagnostic.
    pub fn with_secondary(mut self, span: Span, label: impl Into<String>) -> Self {
        self.labels.push(DiagLabel::secondary(span, label));
        self
    }

    /// Builder method that adds a note to the diagnostic.
    pub fn with_note(mut self, note: impl AsRef<str>) -> Self {
        self.notes.push(format!("note: {}", note.as_ref()));
        self
    }
}

/// Diagnostic context.
///
/// This is used throughout the interpreter to report errors and warnings.
#[derive(Debug, Default)]
pub struct DiagContext {
    pending: Mutex<Vec<Diag>>,
}

impl DiagContext {
    /// Create a new empty diagnostic context.
    pub fn new() -> Self {
        Self::default()
    }

    /// Does the current context contain any errors?
    pub fn has_errors(&self) -> bool {
        self.pending
            .lock()
            .unwrap()
            .iter()
            .any(|d| d.kind == DiagKind::Error)
    }

    /// Add a diagnostic to the context.
    pub fn emit<D: Diagnostic>(&self, diag: D) {
        self.pending.lock().unwrap().push(diag.into_diag());
    }
}

pub mod render {
    //! Diagnostic rendering.

    use codespan_reporting::term::termcolor::{ColorChoice, WriteColor};
    use codespan_reporting::{diagnostic, term};

    use super::*;
    use crate::session::Session;

    /// Render the current session's `DiagContext` to a string.
    pub fn render_dcx() -> String {
        use codespan_reporting::term::termcolor::NoColor;

        use crate::session::Session;

        Session::with_current(|key| {
            let mut buf = NoColor::new(Vec::<u8>::new());
            key.get().dcx.report_to(&mut buf);
            String::from_utf8(buf.into_inner()).unwrap()
        })
    }

    pub(crate) fn render_config() -> term::Config {
        term::Config {
            display_style: term::DisplayStyle::Rich,
            tab_width: 4,
            styles: term::Styles::default(),
            chars: term::Chars::ascii(),
            start_context_lines: 2,
            end_context_lines: 1,
        }
    }

    impl LabelKind {
        fn into_codespan_underline_style(self) -> diagnostic::LabelStyle {
            match self {
                LabelKind::Primary => diagnostic::LabelStyle::Primary,
                LabelKind::Secondary => diagnostic::LabelStyle::Secondary,
            }
        }
    }

    impl DiagLabel {
        pub(crate) fn into_codespan_label(self) -> diagnostic::Label<usize> {
            Session::with_current(|key| {
                let DiagLabel { kind, span, label } = self;
                let source = key.get().sm.span_source(span).unwrap();
                let range = span.range_within(source.span()).unwrap();
                diagnostic::Label::new(kind.into_codespan_underline_style(), source.index(), range)
                    .with_message(label)
            })
        }
    }

    impl Diag {
        pub(crate) fn into_codespan_diagnostic(self) -> diagnostic::Diagnostic<usize> {
            let Diag {
                kind,
                message,
                labels,
                notes,
            } = self;

            let severity = match kind {
                DiagKind::Warning => diagnostic::Severity::Warning,
                DiagKind::Error => diagnostic::Severity::Error,
            };

            let labels = labels
                .into_iter()
                .map(|label| label.into_codespan_label())
                .collect();

            diagnostic::Diagnostic::new(severity)
                .with_message(message)
                .with_labels(labels)
                .with_notes(notes)
        }
    }

    impl DiagContext {
        /// Render all collected diagnostics to standard error.
        pub fn report(&self) {
            let writer = term::termcolor::StandardStream::stderr(ColorChoice::Auto);
            self.report_to(&mut writer.lock());
        }

        /// Render all collected diagnostics to the given stream.
        pub fn report_to(&self, writer: &mut dyn WriteColor) {
            let config = render_config();

            Session::with_current(|key| {
                for diag in self.pending.lock().unwrap().drain(..) {
                    let report = diag.into_codespan_diagnostic();
                    term::emit(writer, &config, &key.get().sm, &report).unwrap();
                }
            });
        }
    }
}

#[cfg(test)]
mod test {
    use codespan_reporting::term;
    use indoc::indoc;

    use super::*;
    use crate::session::Session;

    fn render_diag(diag: Diag) -> String {
        let mut writer = term::termcolor::NoColor::new(Vec::<u8>::new());
        let config = render::render_config();
        let report = diag.into_codespan_diagnostic();
        Session::with_current(|key| {
            term::emit(&mut writer, &config, &key.get().sm, &report).unwrap();
        });
        String::from_utf8(writer.into_inner()).unwrap()
    }

    fn mkmap<'a>(sources: impl IntoIterator<Item = &'a str>) {
        Session::with_current(|key| {
            for (i, source) in sources.into_iter().enumerate() {
                key.get().sm.add_source(i, source);
            }
        });
    }

    #[test]
    fn single_label_single_source() {
        Session::with_default(|key| {
            let source = indoc! {"
            lmao hey() {
                what's() up;
            }"};
            mkmap(Some(source));

            let primary_span = key.get().sm.global_line(1).span_within(4..8).unwrap();

            let diag = Diag::new(DiagKind::Error, "You messed up")
                .with_primary(primary_span, "what's up with this");

            insta::assert_snapshot!(render_diag(diag), @r#"
            error: You messed up
              --> %i0:2:5
              |
            2 |     what's() up;
              |     ^^^^ what's up with this

            "#);
        });
    }

    #[test]
    fn several_labels_single_source() {
        Session::with_default(|key| {
            let source = indoc! {r#"
            fun hey(here, is, some, stuff) {
                things = stuff + 3;
                how("why", some) + oops;
                lol
            }"#};
            mkmap(Some(source));

            let primary_span = key.get().sm.global_line(2).span_within(23..27).unwrap();
            let primary_label = "identifier `oops` is not in scope";

            let diag = Diag::new(DiagKind::Error, "unrecognized identifier `oops`")
                .with_primary(primary_span, primary_label)
                .with_secondary(
                    key.get().sm.global_line(0).span_within(14..16).unwrap(),
                    "there's this thing here, did you mean that?",
                )
                .with_secondary(
                    key.get().sm.global_line(3).span_within(6..7).unwrap(),
                    "forgot something here too lol",
                )
                .with_note("can't use undeclared identifiers bud!")
                .with_note("also lol forgot a semicolon lmao");

            insta::assert_snapshot!(render_diag(diag), @r#"
            error: unrecognized identifier `oops`
              --> %i0:3:24
              |
            1 | fun hey(here, is, some, stuff) {
              |               -- there's this thing here, did you mean that?
            2 |     things = stuff + 3;
            3 |     how("why", some) + oops;
              |                        ^^^^ identifier `oops` is not in scope
            4 |     lol
              |       - forgot something here too lol
              |
              = note: can't use undeclared identifiers bud!
              = note: also lol forgot a semicolon lmao

            "#);
        });
    }

    #[test]
    fn multiple_sources() {
        Session::with_default(|key| {
            mkmap([
                indoc! {"
                a = 4;
                b = 6;

                fun lol() {
                    what even?
                }
                "},
                indoc! {"
                const HEY!;

                foo bar and so forth;
                "},
            ]);

            let diag = Diag::new(DiagKind::Warning, "huh?")
                .with_primary(
                    key.get().sm.source(1).line(2).span_within(8..11).unwrap(),
                    "this one's reserved",
                )
                .with_secondary(
                    key.get().sm.source(0).line(3).span_within(7..9).unwrap(),
                    "empty???",
                )
                .with_secondary(
                    key.get().sm.source(1).line(0).span_within(9..10).unwrap(),
                    "wtf is this",
                );

            insta::assert_snapshot!(render_diag(diag), @r#"
            warning: huh?
              --> %i1:3:9
              |
            1 | const HEY!;
              |          - wtf is this
            2 | 
            3 | foo bar and so forth;
              |         ^^^ this one's reserved
              |
              --> %i0:4:8
              |
            4 | fun lol() {
              |        -- empty???

            "#);
        });
    }
}
