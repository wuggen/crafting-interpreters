use std::ops::Index;
use std::slice::SliceIndex;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    byte_offset: usize,
    len: usize,
}

#[derive(Debug, Clone)]
pub struct Source {
    content: String,
    line_starts: Vec<usize>,
}

impl Source {
    pub fn new(content: String) -> Self {
        let line_starts = content
            .char_indices()
            .zip(content.char_indices().skip(1))
            .filter_map(|((_, c1), (i2, _))| if c1 == '\n' { Some(i2) } else { None })
            .collect();
        Self {
            content,
            line_starts,
        }
    }

    pub fn content(&self) -> &str {
        &self.content
    }

    pub fn line_checked(&self, n: usize) -> Option<&str> {
        let (start, end) = self.line_extents(n)?;
        Some(&self.content[start..end])
    }

    pub fn line(&self, n: usize) -> &str {
        self.line_checked(n).expect("invalid line number")
    }

    pub fn span_checked(&self, span: Span) -> Option<&str> {
        self.content
            .get(span.byte_offset..span.byte_offset + span.len)
    }

    pub fn span(&self, span: Span) -> &str {
        self.span_checked(span).expect("invalid span")
    }

    pub fn line_of(&self, byte_offset: usize) -> Option<usize> {
        self.line_starts.iter().position(|&i| i > byte_offset)
    }

    pub fn position_in_line(&self, byte_offset: usize) -> Option<usize> {
        let line_idx = self.line_of(byte_offset)?;
        let (start, end) = self.line_extents(line_idx)?;
        let line = &self.content[start..end];
        let byte_offset = byte_offset - start;
        line.char_indices().position(|(i, _)| i == byte_offset)
    }

    pub fn source_point_of(&self, byte_offset: usize) -> Option<SourcePoint> {
        let line = self.line_of(byte_offset)?;
        let (start, end) = self.line_extents(line)?;
        let line_content = &self.content[start..end];
        let byte_offset = byte_offset - start;
        let column = line_content
            .char_indices()
            .take_while(|&(i, _)| i <= byte_offset)
            .position(|(i, _)| i == byte_offset)?;
        Some(SourcePoint { line, column })
    }

    pub fn span_source_points(&self, span: Span) -> Option<(SourcePoint, SourcePoint)> {
        let start = self.source_point_of(span.byte_offset)?;
        let end = self.source_point_of(span.byte_offset + span.len)?;
        Some((start, end))
    }

    fn line_extents(&self, n: usize) -> Option<(usize, usize)> {
        if n > self.line_starts.len() {
            None
        } else {
            let start = if n == 0 { 0 } else { self.line_starts[n - 1] };
            let end = if n < self.line_starts.len() {
                self.line_starts[n]
            } else {
                self.content.len()
            };
            Some((start, end))
        }
    }
}

impl<I> Index<I> for Source
where
    I: SliceIndex<str>,
{
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output {
        &self.content[index]
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourcePoint {
    pub line: usize,
    pub column: usize,
}
