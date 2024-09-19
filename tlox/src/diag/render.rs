//use std::cmp::{Ordering, Reverse};
//use std::collections::{BTreeMap, BinaryHeap};
use std::ops::{Add, Sub};

use crate::span::{Line, /*Location, Source*/};

//use super::*;

//pub mod old;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Point {
    pub row: usize,
    pub column: usize,
}

impl Add for Point {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Point {
            row: self.row + rhs.row,
            column: self.column + rhs.column,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Hash)]
pub struct Extents {
    pub rows: usize,
    pub columns: usize,
}

impl Extents {
    pub fn new(rows: usize, columns: usize) -> Self {
        Self { rows, columns }
    }
}

impl Add<Extents> for Point {
    type Output = Point;

    fn add(self, rhs: Extents) -> Self::Output {
        Point {
            row: self.row + rhs.rows,
            column: self.column + rhs.columns,
        }
    }
}

impl Sub for Point {
    type Output = Extents;

    fn sub(self, rhs: Self) -> Self::Output {
        Extents {
            rows: self.row - rhs.row,
            columns: self.column - rhs.column,
        }
    }
}

macro_rules! point {
    ($tt:tt ,) => {
        point!($tt)
    };

    ($row:expr, $column:expr) => {
        Point {
            row: $row,
            column: $column,
        }
    };
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Anchor<T> {
    pub node: T,
    pub anchor: Point,
}

pub trait Anchorable: Sized {
    fn anchored(self, anchor: Point) -> Anchor<Self> {
        Anchor { node: self, anchor }
    }
}

impl<T: Sized> Anchorable for T {}

pub trait PlacementRenderable {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer);

    fn dimensions(&self) -> Extents;
}

pub trait Renderable: PlacementRenderable {
    fn render(&self, buffer: &mut WindowBuffer) {
        self.placement_render(point!(0, 0), buffer);
    }
}

impl<T: PlacementRenderable> Renderable for Anchor<T> {
    fn render(&self, buffer: &mut WindowBuffer) {
        self.node.placement_render(self.anchor, buffer);
    }
}

impl<T: PlacementRenderable> PlacementRenderable for Anchor<T> {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        self.node.placement_render(anchor + self.anchor, buffer);
    }

    fn dimensions(&self) -> Extents {
        self.node.dimensions()
    }
}

impl<T: PlacementRenderable> PlacementRenderable for &T {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        (*self).placement_render(anchor, buffer);
    }

    fn dimensions(&self) -> Extents {
        (*self).dimensions()
    }
}

impl<T: Renderable> Renderable for &T {
    fn render(&self, buffer: &mut WindowBuffer) {
        (*self).render(buffer);
    }
}

impl PlacementRenderable for &str {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        Text::new(self).placement_render(anchor, buffer);
    }

    fn dimensions(&self) -> Extents {
        Text::new(self).dimensions()
    }
}

impl PlacementRenderable for String {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        self.as_str().placement_render(anchor, buffer);
    }

    fn dimensions(&self) -> Extents {
        self.as_str().dimensions()
    }
}

#[derive(Debug, Clone)]
pub struct Text {
    content: String,
    rendered_size: Extents,
}

impl Text {
    pub fn new(content: &str) -> Self {
        if content.is_empty() {
            return Self {
                content: String::new(),
                rendered_size: Extents::default(),
            };
        }

        let mut rendered = String::new();
        let (mut row, mut col, mut max_col) = (0, 0, 0);
        for c in content.chars() {
            match c {
                '\t' => {
                    rendered.push_str("    ");
                    col += 4;
                    max_col = max_col.max(col);
                }

                '\n' => {
                    rendered.push('\n');
                    col = 0;
                    row += 1;
                }

                c => {
                    rendered.push(c);
                    col += 1;
                    max_col = max_col.max(col);
                }
            }
        }

        let rendered_size = Extents {
            rows: row + 1,
            columns: max_col,
        };

        Self {
            content: rendered,
            rendered_size,
        }
    }
}

impl PlacementRenderable for Text {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        let (mut row, mut col) = (0, 0);
        for c in self.content.chars() {
            if c == '\n' {
                row += 1;
                col = 0;
            } else {
                buffer.put_char(anchor + point!(row, col), c);
                col += 1;
            }
        }
    }

    fn dimensions(&self) -> Extents {
        self.rendered_size
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LineSegment {
    orientation: SegmentOrientation,
    len: usize,
}

impl LineSegment {
    pub fn new(orientation: SegmentOrientation, len: usize) -> Self {
        Self { orientation, len }
    }
}

impl PlacementRenderable for LineSegment {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        match self.orientation {
            SegmentOrientation::Vertical => {
                for i in 0..self.len {
                    buffer.put_char(anchor + point!(i, 0), '|');
                }
            }

            SegmentOrientation::Horizontal => {
                for i in 0..self.len {
                    buffer.put_char(anchor + point!(0, i), '_');
                }
            }
        }
    }

    fn dimensions(&self) -> Extents {
        match self.orientation {
            SegmentOrientation::Vertical => Extents::new(self.len, 1),
            SegmentOrientation::Horizontal => Extents::new(1, self.len),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SegmentOrientation {
    Vertical,
    Horizontal,
}

#[derive(Debug, Clone, Copy)]
pub struct Underline {
    kind: UnderlineKind,
    len: usize,
}

impl Underline {
    pub fn new(kind: UnderlineKind, len: usize) -> Self {
        Self { kind, len }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnderlineKind {
    Primary,
    Secondary,
}

impl UnderlineKind {
    pub const fn underline_char(&self) -> char {
        match self {
            UnderlineKind::Primary => '^',
            UnderlineKind::Secondary => '-',
        }
    }
}

impl PlacementRenderable for Underline {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        let c = self.kind.underline_char();
        for i in 0..self.len {
            buffer.put_char(anchor + point!(0, i), c);
        }
    }

    fn dimensions(&self) -> Extents {
        Extents::new(1, self.len)
    }
}

#[derive(Debug, Clone)]
pub struct LineSegments {
    points: Vec<Point>,
}

impl LineSegments {
    pub fn new(start: Point) -> Self {
        Self {
            points: vec![start],
        }
    }

    pub fn push(&mut self, point: Point) {
        let prev = self.points.last().unwrap();
        assert!(
            point.row == prev.row || point.column == prev.column,
            "line segments must be vertical or horizontal"
        );
        self.points.push(point);
    }
}

fn rectify_segments<'a>(mut a: &'a mut Anchor<LineSegment>, mut b: &'a mut Anchor<LineSegment>) {
    if a.node.orientation != b.node.orientation {
        if a.node.orientation != SegmentOrientation::Vertical {
            std::mem::swap(&mut a, &mut b);
        }

        debug_assert!(a.anchor.row <= b.anchor.row);

        if a.anchor.row == b.anchor.row {
            a.node.len -= 1;
            a.anchor.row += 1;
        } else {
            b.node.len -= 1;
            if a.anchor.column == b.anchor.column {
                b.anchor.column += 1;
            }
        }
    }
}

impl PlacementRenderable for LineSegments {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        let mut segments = self
            .points
            .windows(2)
            .map(|pair| {
                let (a, b) = (pair[0], pair[1]);
                debug_assert!(a.row == b.row || a.column == b.column);

                if a.row == b.row {
                    LineSegment::new(
                        SegmentOrientation::Horizontal,
                        a.column.abs_diff(b.column) + 1,
                    )
                } else {
                    LineSegment::new(SegmentOrientation::Vertical, a.row.abs_diff(b.row) + 1)
                }
                .anchored(a.min(b))
            })
            .collect::<Vec<_>>();

        for i in 0..segments.len() - 1 {
            let (a, b) = segments.split_at_mut(i + 1);
            let (a, b) = (a.last_mut().unwrap(), b.first_mut().unwrap());
            rectify_segments(a, b);
        }

        for segment in segments {
            segment.placement_render(anchor, buffer);
        }
    }

    fn dimensions(&self) -> Extents {
        let first_point = *self.points.first().unwrap();
        let init = Extents {
            rows: first_point.row + 1,
            columns: first_point.column + 1,
        };
        self.points[1..].iter().fold(init, |acc, next| Extents {
            rows: acc.rows.max(next.row + 1),
            columns: acc.columns.max(next.column + 1),
        })
    }
}

impl Renderable for LineSegments {}

#[derive(Debug, Clone)]
pub struct OneLineLabel {
    underline: Underline,
    level: usize,
    label: Text,
}

impl OneLineLabel {
    pub fn new(kind: UnderlineKind, len: usize, label: &str) -> Self {
        let underline = Underline::new(kind, len);
        let label = Text::new(label);
        assert_eq!(label.rendered_size.rows, 1, "labels must be one line");
        Self {
            underline,
            level: 0,
            label,
        }
    }
}

impl PlacementRenderable for OneLineLabel {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        self.underline.placement_render(anchor, buffer);

        let text_anchor = if self.level == 0 {
            point!(0, self.underline.len + 1)
        } else {
            let subline = LineSegment::new(SegmentOrientation::Vertical, 2 * self.level - 1)
                .anchored(point!(1, 0));
            subline.placement_render(anchor, buffer);
            point!(2 * self.level, 0)
        };

        self.label.placement_render(anchor + text_anchor, buffer);
    }

    fn dimensions(&self) -> Extents {
        let underline_dims = self.underline.dimensions();
        let label_dims = self.label.dimensions();

        if self.level == 0 {
            Extents {
                rows: label_dims.rows,
                columns: underline_dims.columns + label_dims.columns + 1,
            }
        } else {
            Extents {
                rows: 2 * self.level + label_dims.rows,
                columns: underline_dims.columns.max(label_dims.columns),
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct SourceLine {
    text: Text,
    index: usize,
    labels: Vec<Anchor<OneLineLabel>>,
}

impl SourceLine {
    pub fn new(line: Line) -> Self {
        let text = Text::new(line.content());
        let index = line.index_in_source();
        Self {
            text,
            index,
            labels: vec![],
        }
    }

    pub fn push_label(&mut self, col: usize, label: OneLineLabel) {
        for label in &mut self.labels {
            label.node.level += 1;
        }

        if let Some(prev) = self.labels.last_mut() {
            assert!(
                prev.anchor.column < col,
                "labels must be added to lines in order"
            );

            // TODO: handle overlapping spans, maybe
        }

        self.labels.push(label.anchored(point!(1, col)));
    }
}

impl PlacementRenderable for SourceLine {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        self.text.placement_render(anchor, buffer);
        for label in &self.labels {
            label.placement_render(anchor, buffer);
        }
    }

    fn dimensions(&self) -> Extents {
        let mut dims = self.text.dimensions();
        for label in &self.labels {
            let label_dims = label.node.dimensions();
            dims.rows = dims.rows.max(1 + label_dims.rows);
            dims.columns = dims.columns.max(label.anchor.column + label_dims.columns);
        }

        dims
    }
}

#[derive(Debug, Clone, Default)]
pub struct SourceWindow {
    lines: Vec<Anchor<SourceLine>>,
    gaps: usize,
}

impl SourceWindow {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push_line(&mut self, line: SourceLine) {
        let anchor = if let Some(prev) = self.lines.last() {
            assert!(
                prev.node.index < line.index,
                "source lines must be added to windows in order"
            );

            if prev.node.index < line.index - 1 {
                self.gaps += 1;
            }

            let prev_dims = prev.node.dimensions();
            point!(prev.anchor.row + prev_dims.rows, 0)
        } else {
            point!(0, 0)
        };

        self.lines.push(line.anchored(anchor));
    }

    fn max_line_num_digits(&self) -> usize {
        if let Some(last) = self.lines.last() {
            num_decimal_digits(last.node.index + 1)
        } else {
            0
        }
    }

    fn gutter_width(&self) -> usize {
        self.max_line_num_digits() + 1
    }

    fn margin_width(&self) -> usize {
        1
    }

    fn total_margin(&self) -> usize {
        self.gutter_width() + self.margin_width() + 1
    }
}

fn num_decimal_digits(mut n: usize) -> usize {
    if n == 0 {
        1
    } else {
        let mut digits = 0;
        while n > 0 {
            n /= 10;
            digits += 1;
        }
        digits
    }
}

impl PlacementRenderable for SourceWindow {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        if self.lines.is_empty() {
            return;
        }

        let last = self.lines.last().unwrap();
        let margin_line_len = last.anchor.row + last.node.dimensions().rows + self.gaps;
        let margin_line_col = self.max_line_num_digits() + 1;
        let line_anchor = point!(0, margin_line_col + 2);

        LineSegment::new(SegmentOrientation::Vertical, margin_line_len)
            .anchored(point!(0, margin_line_col))
            .placement_render(anchor, buffer);

        let mut additional = point!(0, 0);
        for (i, line) in self.lines.iter().enumerate() {
            format!("{}", line.node.index + 1)
                .anchored(line.anchor + additional)
                .placement_render(anchor, buffer);
            line.anchored(line_anchor + additional)
                .placement_render(anchor, buffer);

            if i + 1 < self.lines.len() && self.lines[i + 1].node.index > line.node.index + 1 {
                "..."
                    .anchored(point!(
                        line.anchor.row + line.node.dimensions().rows,
                        margin_line_col - 1
                    ))
                    .placement_render(anchor, buffer);
                additional.row += 1;
            }
        }
    }

    fn dimensions(&self) -> Extents {
        if self.lines.is_empty() {
            return Extents::default();
        }

        let margin = self.total_margin();
        let columns = self
            .lines
            .iter()
            .map(|line| line.node.dimensions().columns + margin)
            .max()
            .unwrap();
        let last = self.lines.last().unwrap();
        let rows = last.anchor.row + last.dimensions().rows + self.gaps;
        Extents { rows, columns }
    }
}

#[derive(Debug, Clone)]
pub struct DiagWindow {
    message: Text,
    primary: Text,
    source: SourceWindow,
    notes: Vec<Text>,
}

impl DiagWindow {
    pub fn new(message: &str, primary: &str) -> Self {
        Self {
            message: Text::new(message),
            primary: Text::new(primary),
            source: SourceWindow::new(),
            notes: vec![],
        }
    }

    pub fn source_window(&mut self) -> &mut SourceWindow {
        &mut self.source
    }

    pub fn add_note(&mut self, note: &str) {
        self.notes.push(Text::new(note));
    }
}

impl PlacementRenderable for DiagWindow {
    fn placement_render(&self, anchor: Point, buffer: &mut WindowBuffer) {
        self.message.placement_render(anchor, buffer);

        let mut row = self.message.dimensions().rows;
        "==>".placement_render(point!(row, 0), buffer);
        self.primary.placement_render(point!(row, 4), buffer);

        row += self.primary.dimensions().rows.max(1);
        self.source
            .placement_render(anchor + point!(row, 0), buffer);

        row += self.source.dimensions().rows;
        for note in &self.notes {
            "note:".placement_render(anchor + point!(row, 0), buffer);
            note.placement_render(anchor + point!(row, 6), buffer);
            row += note.dimensions().rows.max(1);
        }
    }

    fn dimensions(&self) -> Extents {
        let message_dims = self.message.dimensions();
        let primary_text_dims = self.primary.dimensions();
        let primary_dims = Extents {
            rows: primary_text_dims.rows.max(1),
            columns: primary_text_dims.columns + 4,
        };
        let source_dims = self.source.dimensions();
        let notes_dims = self.notes.iter().fold(Extents::default(), |mut acc, note| {
            let note_dims = note.dimensions();
            acc.rows += note_dims.rows;
            acc.columns = acc.columns.max(note_dims.columns + 6);
            acc
        });

        Extents {
            rows: message_dims.rows + primary_dims.rows + source_dims.rows + notes_dims.rows,
            columns: message_dims
                .columns
                .max(primary_dims.columns)
                .max(source_dims.columns)
                .max(notes_dims.columns),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct WindowBuffer {
    lines: Vec<Vec<char>>,
}

impl WindowBuffer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn put_char(&mut self, point: Point, c: char) {
        let Point { row, column } = point;

        if self.lines.len() <= row {
            self.lines.resize_with(row + 1, Default::default);
        }

        if self.lines[row].len() <= column {
            self.lines[row].resize(column + 1, ' ');
        }

        self.lines[row][column] = c;
    }

    pub fn finalize(&self) -> String {
        let mut output = String::new();
        for line in &self.lines {
            output.extend(line.iter().copied());
            output.push('\n');
        }
        output
    }
}

/// Converts horizontal tabs to spaces for the purposes of rendering.
pub fn render_str(input: &str) -> String {
    let mut output = String::new();
    for c in input.chars() {
        if c == '\t' {
            output.push_str("    ");
        } else {
            output.push(c);
        }
    }
    output
}

#[cfg(test)]
mod test {
    use super::*;

    fn render<T: PlacementRenderable>(node: &T) -> String {
        let mut buffer = WindowBuffer::new();
        node.placement_render(point!(0, 0), &mut buffer);
        buffer.finalize()
    }

    fn assert_same_render<T: PlacementRenderable>(node: &T, expected: &str) {
        let mut rendered = render(node);
        if !rendered.is_empty() && rendered.get(rendered.len() - 1..) == Some("\n") {
            rendered.pop();
        }

        let expected_dimensions = {
            let (mut rows, mut columns) = (0, 0);
            for line in expected.lines() {
                rows += 1;
                columns = columns.max(line.chars().count());
            }
            Extents { rows, columns }
        };
        let reported_dimensions = node.dimensions();

        if expected_dimensions != reported_dimensions || rendered != expected {
            eprintln!("!! Different renders and/or reported dimensions");
            eprintln!("== Expected render (dims {expected_dimensions:?}):");
            for line in expected.lines() {
                eprintln!("#\"{line}\"#");
            }
            eprintln!("\n== Actual render (reported dims {reported_dimensions:?}):");
            for line in rendered.lines() {
                eprintln!("#\"{line}\"#");
            }
            panic!("mismatched renders");
        }
    }

    #[test]
    fn line_segments() {
        let mut segments = LineSegments::new(point!(0, 0));
        segments.push(point!(2, 0));
        segments.push(point!(2, 3));
        segments.push(point!(1, 3));

        let expected = r#"|
|  |
|__|"#;
        assert_same_render(&segments, expected);

        let mut segments = LineSegments::new(point!(0, 3));
        segments.push(point!(0, 1));
        segments.push(point!(2, 1));
        let expected = r#" ___
 |
 |"#;
        assert_same_render(&segments, expected);

        let mut segments = LineSegments::new(point!(2, 0));
        segments.push(point!(0, 0));
        segments.push(point!(0, 2));
        segments.push(point!(2, 2));
        segments.push(point!(2, 4));
        let expected = r#"___
| |
| |__"#;
        assert_same_render(&segments, expected);
    }

    use SegmentOrientation::*;
    use UnderlineKind::*;

    #[test]
    fn underlines() {
        let line = Underline::new(Primary, 3);
        assert_same_render(&line, "^^^");

        let line = Underline::new(Secondary, 5);
        assert_same_render(&line, "-----");
    }

    #[test]
    fn strings() {
        let text = "lmao hey";
        assert_same_render(&text, text);

        let text = "";
        assert_same_render(&text, text);
    }

    #[test]
    fn individual_segments() {
        let segment = LineSegment::new(Vertical, 3);
        assert_same_render(&segment, "|\n|\n|");

        let segment = LineSegment::new(Horizontal, 5);
        assert_same_render(&segment, "_____");
    }

    #[test]
    fn one_line_labels() {
        let mut label = OneLineLabel::new(Primary, 3, "hey");
        assert_same_render(&label, "^^^ hey");

        label.level = 1;
        assert_same_render(
            &label,
            r#"^^^
|
hey"#,
        );

        label.level = 2;
        assert_same_render(
            &label,
            r#"^^^
|
|
|
hey"#,
        );

        label.underline.kind = Secondary;
        label.underline.len = 5;
        label.level = 0;
        assert_same_render(&label, "----- hey");

        label.label = Text::new("lol what's up");
        assert_same_render(&label, "----- lol what's up");
    }

    #[test]
    fn source_lines() {
        use UnderlineKind::*;
        let mut source_line = SourceLine {
            text: Text::new("heya here's some code"),
            index: 0,
            labels: vec![],
        };

        source_line.push_label(5, OneLineLabel::new(Primary, 4, "what's up lol and &c"));
        assert_same_render(
            &source_line,
            r#"heya here's some code
     ^^^^ what's up lol and &c"#,
        );

        source_line.push_label(12, OneLineLabel::new(Secondary, 4, "lmao???"));
        assert_same_render(
            &source_line,
            r#"heya here's some code
     ^^^^   ---- lmao???
     |
     what's up lol and &c"#,
        );

        source_line.push_label(17, OneLineLabel::new(Secondary, 1, "incorrect"));
        assert_same_render(
            &source_line,
            r#"heya here's some code
     ^^^^   ---- - incorrect
     |      |
     |      lmao???
     |
     what's up lol and &c"#,
        );
    }

    #[test]
    fn source_windows() {
        use UnderlineKind::*;
        let mut window = SourceWindow::new();

        window.push_line(SourceLine {
            text: Text::new("here's some code"),
            index: 2,
            labels: vec![],
        });
        window.lines[0]
            .node
            .push_label(7, OneLineLabel::new(Secondary, 4, "messed up"));
        assert_same_render(
            &window,
            r#"3 | here's some code
  |        ---- messed up"#,
        );

        window.lines[0]
            .node
            .push_label(12, OneLineLabel::new(Primary, 4, "lol idiot"));
        assert_same_render(
            &window,
            r#"3 | here's some code
  |        ---- ^^^^ lol idiot
  |        |
  |        messed up"#,
        );

        window.push_line(SourceLine {
            text: Text::new("\tand some more"),
            index: 3,
            labels: vec![],
        });
        window.push_line(SourceLine {
            text: Text::new("\t\tand even more!"),
            index: 10,
            labels: vec![],
        });

        window.lines[2]
            .node
            .push_label(21, OneLineLabel::new(Secondary, 1, "cmon man"));

        assert_same_render(
            &window,
            r#"3  | here's some code
   |        ---- ^^^^ lol idiot
   |        |
   |        messed up
4  |     and some more
  ...
11 |         and even more!
   |                      - cmon man"#,
        );
    }

    #[test]
    fn diag_windows() {
        let mut window = DiagWindow::new("error: lmao dude what", "file:here:there");
        assert_same_render(
            &window,
            r#"error: lmao dude what
==> file:here:there"#,
        );

        window.add_note("cmon man are you serious lol");
        assert_same_render(
            &window,
            r#"error: lmao dude what
==> file:here:there
note: cmon man are you serious lol"#,
        );

        let mut line = SourceLine {
            text: Text::new("heya from the code lmfao"),
            index: 99,
            labels: vec![],
        };
        line.push_label(19, OneLineLabel::new(Secondary, 5, "roflmao"));
        window.source_window().push_line(line);
        assert_same_render(
            &window,
            r#"error: lmao dude what
==> file:here:there
100 | heya from the code lmfao
    |                    ----- roflmao
note: cmon man are you serious lol"#,
        );

        let mut line = SourceLine {
            text: Text::new("\t\twtf man"),
            index: 110,
            labels: vec![],
        };
        line.push_label(0, OneLineLabel::new(Primary, 8, "seriously dude?"));
        line.push_label(12, OneLineLabel::new(Secondary, 3, "gender!!!"));
        window.source_window().push_line(line);

        assert_same_render(
            &window,
            r#"error: lmao dude what
==> file:here:there
100 | heya from the code lmfao
    |                    ----- roflmao
   ...
111 |         wtf man
    | ^^^^^^^^    --- gender!!!
    | |
    | seriously dude?
note: cmon man are you serious lol"#,
        );
    }
}
