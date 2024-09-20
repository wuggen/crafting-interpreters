//! Errors and diagnostics.

#![allow(missing_docs)]

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
}

pub mod render {
    use super::*;

    use codespan_reporting::term::termcolor::ColorChoice;
    use codespan_reporting::{diagnostic, term};

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

    impl DiagLabel {
        pub(crate) fn into_codespan_label(
            self,
            kind: diagnostic::LabelStyle,
            map: &SourceMap,
        ) -> diagnostic::Label<usize> {
            let DiagLabel { span, label } = self;
            let source = map.span_source(span).unwrap();
            let range = span.range_within(source.span()).unwrap();
            diagnostic::Label::new(kind, source.index(), range).with_message(label)
        }
    }

    impl Diag {
        pub(crate) fn into_codespan_diagnostic(
            self,
            map: &SourceMap,
        ) -> diagnostic::Diagnostic<usize> {
            let Diag {
                kind,
                message,
                primary,
                secondary,
                notes,
            } = self;

            let severity = match kind {
                DiagKind::Warning => diagnostic::Severity::Warning,
                DiagKind::Error => diagnostic::Severity::Error,
            };

            let mut labels =
                vec![primary.into_codespan_label(diagnostic::LabelStyle::Primary, map)];
            labels.extend(
                secondary
                    .into_iter()
                    .map(|label| label.into_codespan_label(diagnostic::LabelStyle::Secondary, map)),
            );

            diagnostic::Diagnostic::new(severity)
                .with_message(message)
                .with_labels(labels)
                .with_notes(notes)
        }
    }

    impl DiagContext {
        pub fn report(&mut self, source_map: &SourceMap) {
            let writer = term::termcolor::StandardStream::stderr(ColorChoice::Auto);
            let config = render_config();

            for diag in self.pending.drain(..) {
                let report = diag.into_codespan_diagnostic(source_map);
                term::emit(&mut writer.lock(), &config, source_map, &report).unwrap();
            }
        }
    }
}

#[cfg(test)]
mod test {
    use codespan_reporting::term;
    use indoc::indoc;

    use super::*;

    fn render_diag<'a>(diag: Diag, map: &SourceMap) -> String {
        let mut writer = term::termcolor::NoColor::new(Vec::<u8>::new());
        let config = render::render_config();
        let report = diag.into_codespan_diagnostic(&map);
        term::emit(&mut writer, &config, map, &report).unwrap();
        String::from_utf8(writer.into_inner()).unwrap()
    }

    fn mkmap<'a>(sources: impl IntoIterator<Item = &'a str>) -> SourceMap {
        let mut map = SourceMap::new();
        for (i, source) in sources.into_iter().enumerate() {
            map.add_source(i, source);
        }
        map
    }

    #[test]
    fn single_label_single_source() {
        let source = indoc! {"
        lmao hey() {
            what's() up;
        }"};
        let map = mkmap(Some(source));

        let primary_span = map.global_line(1).span_within(4..8).unwrap();
        let diag = Diag::new(
            DiagKind::Error,
            "You messed up",
            primary_span,
            "what's up with this",
        );

        insta::assert_snapshot!(render_diag(diag, &map), @r#"
        error: You messed up
          --> %i0:2:5
          |
        2 |     what's() up;
          |     ^^^^ what's up with this

        "#);
    }

    #[test]
    fn several_labels_single_source() {
        let source = indoc! {r#"
        fun hey(here, is, some, stuff) {
            things = stuff + 3;
            how("why", some) + oops;
            lol
        }"#};
        let map = mkmap(Some(source));

        let primary_span = map.global_line(2).span_within(23..27).unwrap();
        let primary_label = "identifier `oops` is not in scope";

        let diag = Diag::new(
            DiagKind::Error,
            "unrecognized identifier `oops`",
            primary_span,
            primary_label,
        )
        .with_secondary(
            map.global_line(0).span_within(14..16).unwrap(),
            "there's this thing here, did you mean that?",
        )
        .with_secondary(
            map.global_line(3).span_within(6..7).unwrap(),
            "forgot something here too lol",
        )
        .with_note("can't use undeclared identifiers bud!")
        .with_note("also lol forgot a semicolon lmao");

        insta::assert_snapshot!(render_diag(diag, &map), @r#"
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
          = can't use undeclared identifiers bud!
          = also lol forgot a semicolon lmao

        "#);
    }

    #[test]
    fn multiple_sources() {
        let map = mkmap([
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

        let diag = Diag::new(
            DiagKind::Warning,
            "huh?",
            map.source(1).line(2).span_within(8..11).unwrap(),
            "this one's reserved",
        )
        .with_secondary(map.source(0).line(3).span_within(7..9).unwrap(), "empty???")
        .with_secondary(map.source(1).line(0).span_within(9..10).unwrap(), "wtf is this");

        insta::assert_snapshot!(render_diag(diag, &map), @r#"
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
    }
}
