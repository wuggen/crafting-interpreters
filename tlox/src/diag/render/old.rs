use super::*;

#[derive(Debug, Clone, Copy)]
pub struct Underline {
    kind: UnderlineKind,
    len: usize,
}

#[derive(Debug, Clone)]
pub enum Annotation {
    SingleLine {
        start: usize,
        len: usize,
        label_level: usize,
        label: String,
    },

    MultiLineStart {
        point: usize,
        backline_level: usize,
        multi_line_id: usize,
    },

    MultiLineEnd {
        point: usize,
        backline_level: usize,
        multi_line_id: usize,
        label_level: usize,
        label: String,
    },
}

impl Annotation {
    pub fn start(&self) -> usize {
        match self {
            Self::SingleLine { start, .. } => *start,
            Self::MultiLineStart { point, .. } | Self::MultiLineEnd { point, .. } => *point,
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Self::SingleLine { len, .. } => *len,
            _ => 1,
        }
    }

    pub fn end(&self) -> usize {
        self.start() + self.len() - 1
    }

    pub fn set_start(&mut self, new_start: usize) {
        match self {
            Annotation::SingleLine { start, .. } => {
                *start = new_start;
            }

            Annotation::MultiLineStart { point, .. } | Annotation::MultiLineEnd { point, .. } => {
                *point = new_start;
            }
        }
    }

    pub fn set_end(&mut self, new_end: usize) {
        match self {
            Annotation::SingleLine { start, len, .. } => {
                *len = new_end + 1 - *start;
            }

            _ => {}
        }
    }

    pub fn label_level(&self) -> Option<usize> {
        match self {
            Annotation::SingleLine { label_level, .. }
            | Annotation::MultiLineEnd { label_level, .. } => Some(*label_level),
            _ => None,
        }
    }

    pub fn set_label_level(&mut self, level: usize) {
        match self {
            Annotation::SingleLine { label_level, .. }
            | Annotation::MultiLineEnd { label_level, .. } => {
                *label_level = level;
            }
            _ => {}
        }
    }

    pub fn backline_level(&self) -> Option<usize> {
        match self {
            Annotation::MultiLineStart { backline_level, .. }
            | Annotation::MultiLineEnd { backline_level, .. } => Some(*backline_level),
            _ => None,
        }
    }

    pub fn set_backline_level(&mut self, level: usize) {
        match self {
            Annotation::MultiLineStart { backline_level, .. }
            | Annotation::MultiLineEnd { backline_level, .. } => {
                *backline_level = level;
            }
            _ => {}
        }
    }

    pub fn is_endpoint(&self) -> bool {
        matches!(
            self,
            Annotation::MultiLineStart { .. } | Annotation::MultiLineEnd { .. },
        )
    }

    pub fn has_label(&self) -> bool {
        matches!(
            self,
            Annotation::SingleLine { .. } | Annotation::MultiLineEnd { .. },
        )
    }

    pub fn label(&self) -> Option<&str> {
        match self {
            Annotation::SingleLine { label, .. } | Annotation::MultiLineEnd { label, .. } => {
                Some(label)
            }
            _ => None,
        }
    }
}

pub struct AnnotatedSourceLine<'sm> {
    line: Line<'sm>,
    annotations: Vec<(Annotation, UnderlineKind)>,
    num_sub_levels: usize,
}

fn cmp_annotations(a: &Annotation, b: &Annotation) -> Ordering {
    let a_range = a.start()..a.end() + 1;

    if a_range.contains(&b.start()) || a_range.contains(&b.end()) {
        a.len()
            .cmp(&b.len())
            .then_with(|| a.end().cmp(&b.end()))
            .then_with(|| b.start().cmp(&a.start()))
    } else {
        a.start().cmp(&b.start())
    }
}

impl AnnotatedSourceLine<'_> {
    pub fn insert_annotation(&mut self, mut annotation: Annotation, underline_kind: UnderlineKind) {
        let pos = self
            .annotations
            .binary_search_by(|(ann, _)| cmp_annotations(ann, &annotation))
            .err()
            .unwrap();

        if pos > 0 {
            let prev_ann = &mut self.annotations[pos - 1].0;
            if prev_ann.end() >= annotation.start() {
                if prev_ann.len() < annotation.len() {
                    annotation.set_start(prev_ann.end() + 1);
                } else {
                    prev_ann.set_end(annotation.start() - 1);
                }
            }
        }

        if pos < self.annotations.len() {
            let next_ann = &mut self.annotations[pos].0;
            if next_ann.start() <= annotation.end() {
                // Less or equal here, for symmetry with the above, I guess :P
                if next_ann.len() <= annotation.len() {
                    annotation.set_end(next_ann.start() - 1);
                } else {
                    next_ann.set_start(annotation.end() + 1);
                }
            }
        }

        self.annotations.insert(pos, (annotation, underline_kind));
    }

    fn initial_backline_level(&self) -> usize {
        self.annotations
            .first()
            .map(|(ann, _)| if ann.is_endpoint() { 0 } else { 1 })
            .unwrap_or(0)
    }

    fn initial_label_level(&self) -> usize {
        self.annotations
            .last()
            .map(|(ann, _)| if ann.has_label() { 0 } else { 1 })
            .unwrap_or(0)
    }

    fn staircase_backlines(&mut self) {
        let mut level = self.initial_backline_level();
        for ann in
            self.annotations
                .iter_mut()
                .filter_map(|(ann, _)| if ann.is_endpoint() { Some(ann) } else { None })
        {
            ann.set_backline_level(level);
            level += 1;
            self.num_sub_levels = self.num_sub_levels.max(level);
        }
    }

    fn staircase_labels(&mut self) {
        let mut level = self.initial_label_level();
        for (ann, _) in self.annotations.iter_mut().rev() {
            ann.set_label_level(level);
            if let Some(backline_level) = ann.backline_level() {
                level = backline_level + 1;
            } else {
                level += 1;
                self.num_sub_levels = self.num_sub_levels.max(level);
            }
        }
    }

    fn assign_margin_lines(
        &self,
        margin_levels: &mut Vec<usize>,
        free_levels: &mut BinaryHeap<Reverse<usize>>,
        next_level: &mut usize,
    ) {
        for ann in
            self.annotations
                .iter()
                .filter_map(|(ann, _)| if ann.is_endpoint() { Some(ann) } else { None })
        {
            match ann {
                Annotation::MultiLineStart { multi_line_id, .. } => {
                    if let Some(Reverse(level)) = free_levels.pop() {
                        margin_levels[*multi_line_id] = level;
                    } else {
                        margin_levels[*multi_line_id] = *next_level;
                        *next_level += 1;
                    }
                }

                Annotation::MultiLineEnd { multi_line_id, .. } => {
                    free_levels.push(Reverse(margin_levels[*multi_line_id]));
                }

                _ => unreachable!(),
            }
        }
    }

    fn place_annotations(
        &mut self,
        margin_levels: &mut Vec<usize>,
        free_levels: &mut BinaryHeap<Reverse<usize>>,
        next_level: &mut usize,
    ) {
        self.staircase_backlines();
        self.staircase_labels();
        self.assign_margin_lines(margin_levels, free_levels, next_level);
    }

    ///// Returns the next unused line after rendering the underlines, labels, and backlines of this
    ///// line.
    //fn draw(
    //    &self,
    //    buffer: &mut WindowBuffer,
    //    margin_levels: &[usize],
    //    gutter: usize,
    //    margin: usize,
    //    start_row: usize,
    //) -> usize {
    //    buffer.put_line(start_row, self.line, gutter, margin);
    //    for i in 0..self.num_sub_levels {
    //        buffer.put_buffer_line(start_row + 1 + (i * 2), gutter);
    //        buffer.put_buffer_line(start_row + 2 + (i * 2), gutter);
    //    }

    //    for (ann, kind) in self.annotations.iter().rev() {
    //        let column = ann.start() + gutter + margin + 2;
    //        buffer.put_underline(
    //            Point {
    //                row: start_row + 1,
    //                column,
    //            },
    //            ann.len(),
    //            *kind,
    //        );

    //        if let Some(label_level) = ann.label_level() {
    //            if label_level == 0 {
    //                let column = column + ann.len() + 1;
    //                buffer.put_str(
    //                    Point {
    //                        row: start_row + 1,
    //                        column,
    //                    },
    //                    ann.label().unwrap(),
    //                );
    //            } else {
    //                buffer.put_vertical_segment(
    //                    Point {
    //                        row: start_row + 2,
    //                        column,
    //                    },
    //                    (label_level - 1) * 2 + 1,
    //                );
    //                buffer.put_str(
    //                    Point {
    //                        row: start_row + label_level * 2 + 1,
    //                        column,
    //                    },
    //                    ann.label().unwrap(),
    //                );
    //            }
    //        }
    //    }

    //    todo!()
    //}
}

impl<'sm> AnnotatedSourceLine<'sm> {
    pub fn new(line: Line<'sm>) -> Self {
        Self {
            line,
            annotations: vec![],
            num_sub_levels: 0,
        }
    }
}

pub struct SourceWindow<'sm> {
    source: Source<'sm>,
    lines: BTreeMap<usize, AnnotatedSourceLine<'sm>>,
    multi_line_margin_levels: Vec<usize>,
    primary: Option<Location>,
    num_margin_levels: usize,
}

impl<'sm> SourceWindow<'sm> {
    pub fn add_single_line(&mut self, span: Span, primary: bool, label: String) {
        let (start, end) = self.source.map().span_extents(span).unwrap();
        debug_assert_eq!((start.source, start.line), (end.source, end.line));
        debug_assert_eq!(start.source, self.source.index());

        let annotation = Annotation::SingleLine {
            start: start.column,
            len: span.len(),
            label_level: 0,
            label,
        };

        let underline_kind = if primary {
            self.primary = Some(start);
            UnderlineKind::Primary
        } else {
            UnderlineKind::Secondary
        };

        self.line(start.line)
            .insert_annotation(annotation, underline_kind);
    }

    pub fn add_multi_line(&mut self, span: Span, primary: bool, label: String) {
        let (start, end) = self.source.map().span_extents(span).unwrap();
        debug_assert_eq!(start.source, end.source);
        debug_assert!(start.line < end.line);
        debug_assert_eq!(start.source, self.source.index());

        let multi_line_id = self.multi_line_margin_levels.len();
        self.multi_line_margin_levels.push(0);

        let start_ann = Annotation::MultiLineStart {
            point: start.column,
            backline_level: 0,
            multi_line_id,
        };

        let end_ann = Annotation::MultiLineEnd {
            point: end.column,
            backline_level: 0,
            multi_line_id,
            label_level: 0,
            label,
        };

        let underline_kind = if primary {
            self.primary = Some(start);
            UnderlineKind::Primary
        } else {
            UnderlineKind::Secondary
        };

        self.line(start.line)
            .insert_annotation(start_ann, underline_kind);
        self.line(end.line)
            .insert_annotation(end_ann, underline_kind);
        self.line(start.line + 1);
        self.line(end.line - 1);
    }

    pub fn line(&mut self, line: usize) -> &mut AnnotatedSourceLine<'sm> {
        self.lines
            .entry(line)
            .or_insert_with(|| AnnotatedSourceLine::new(self.source.line(line)))
    }

    pub fn place_annotations(&mut self) {
        let mut free_levels = BinaryHeap::new();
        let mut next_level = 0;

        for (_, line) in self.lines.iter_mut() {
            line.place_annotations(
                &mut self.multi_line_margin_levels,
                &mut free_levels,
                &mut next_level,
            );
        }

        self.num_margin_levels = next_level;
    }

    fn gutter_space(&self) -> usize {
        let max_line_num = self
            .lines
            .last_key_value()
            .map(|(k, _)| *k + 1)
            .unwrap_or(0);
        num_decimal_digits(max_line_num) + 1
    }

    fn margin_space(&self) -> usize {
        1 + 2 * self.num_margin_levels
    }

    //pub fn draw(&self, buffer: &mut WindowBuffer, line: usize) {
    //    let gutter = self.gutter_space();
    //    let margin = self.margin_space();

    //    let source_name_pos = if let Some(pos) = self.primary {
    //        format!(
    //            "==> {}:{}:{}",
    //            self.source.name(),
    //            pos.line + 1,
    //            pos.column + 1
    //        )
    //    } else {
    //        format!("==> {}", self.source.name())
    //    };

    //    buffer.put_str(
    //        Point {
    //            row: line,
    //            column: gutter - 1,
    //        },
    //        &source_name_pos,
    //    );
    //    buffer.put_buffer_line(line + 1, gutter);

    //    todo!()
    //}
}

/// Converts a byte offset within a string slice to a render offset in which tabs are replaced with
/// spaces.
pub fn byte_offset_to_render_offset(input: &str, byte_offset: usize) -> usize {
    let mut render_offset = byte_offset;
    for (i, c) in input.char_indices() {
        if i >= byte_offset {
            break;
        }

        if c == '\t' {
            render_offset += 3;
        }
    }
    render_offset
}
