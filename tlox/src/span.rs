//! Source code representations and spans.
//!
//! This module defines two major types:
//!
//! - [`SourceMap`], a map of all sources in the current program, be they files or REPL inputs.
//! - [`Span`], a range of characters within a source map.
//!
//! These, along with supporting types [`Source`], [`Line`], and [`Location`], allow uniform lookup
//! and — in particular! — efficient, constant-size storage and copying of segments of code.

use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::iter::FusedIterator;
use std::ops::Range;
use std::path::PathBuf;

#[cfg(test)]
mod test;

/// A byte span within a [`SourceMap`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    byte_offset: usize,
    len: usize,
}

impl Span {
    /// Get the starting byte offset of this span.
    ///
    /// NB: This is a _global_ offset within the source map.
    pub fn start(&self) -> usize {
        self.byte_offset
    }

    /// Get the byte length of this span.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Is this span empty?
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Get the ending (exclusive) byte offset of this span.
    ///
    /// NB: This is a _global_ offset within the source map.
    pub fn end(&self) -> usize {
        self.start() + self.len()
    }

    /// Get the byte range of this span.
    ///
    /// NB: This range represents _global_ byte offsets within the source map.
    pub fn range(&self) -> Range<usize> {
        self.start()..self.end()
    }
}

/// An item with an associated span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

/// Types to which a [`Span`] can be attached.
///
/// This is blanket implemented for all [`Sized`] types.
pub trait Spannable: Sized {
    /// Attach a span.
    fn spanned(self, span: Span) -> Spanned<Self> {
        Spanned { node: self, span }
    }
}

impl<T: Sized> Spannable for T {}

/// A collection of input source code.
///
/// A source map stores the complete contents of every source, including files and REPL inputs, and
/// allows source code locations and spans to be treated uniformly across all sources.
#[derive(Debug, Default)]
pub struct SourceMap {
    content: String,
    lines: Vec<Span>,
    sources: Vec<(SourceName, Range<usize>)>,
}

/// The name of a source.
///
/// A source is either a file with a file system path, or a REPL input with a zero-based index.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SourceName {
    File(PathBuf),
    ReplInput(usize),
}

impl Display for SourceName {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            SourceName::File(path) => Display::fmt(&path.display(), f),
            SourceName::ReplInput(n) => write!(f, "%i{n}"),
        }
    }
}

impl From<PathBuf> for SourceName {
    fn from(value: PathBuf) -> Self {
        Self::File(value)
    }
}

impl From<usize> for SourceName {
    fn from(value: usize) -> Self {
        Self::ReplInput(value)
    }
}

impl SourceMap {
    /// Convenience method that clones the line index range for a source.
    fn source_info(&self, source: usize) -> Option<(&SourceName, Range<usize>)> {
        self.sources
            .get(source)
            .map(|(name, range)| (name, range.clone()))
    }

    /// Find the global index of the line containing the given byte offset.
    ///
    /// This method operates via binary search on the line spans.
    fn index_of_global_line_containing_offset(&self, byte_offset: usize) -> Option<usize> {
        self.lines
            .binary_search_by(|span| {
                if byte_offset < span.start() {
                    Ordering::Greater
                } else if byte_offset < span.end() {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            })
            .ok()
    }

    /// Find the index of the source containing the given global line index.
    ///
    /// This method operates via binary search on the source ranges.
    fn index_of_source_containing_global_line(&self, line_index: usize) -> Option<usize> {
        self.sources
            .binary_search_by(|(_, range)| {
                if line_index < range.start {
                    Ordering::Greater
                } else if line_index < range.end {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            })
            .ok()
    }
}

impl SourceMap {
    /// Create a new, empty source map.
    pub fn new() -> Self {
        Self::default()
    }

    /// Append a source to the source map.
    ///
    /// If the source does not have a trailing newline, one will be appended, so that all lines in
    /// the source map are terminated with a newline.
    ///
    /// Returns the index of the newly added source.
    pub fn add_source(&mut self, name: impl Into<SourceName>, content: &str) -> usize {
        let current_len = self.content.len();

        self.content.push_str(content);
        if content.get(content.len() - 1..) != Some("\n") {
            self.content.push('\n');
        }

        let mut line_start = 0;
        let lines = content.lines().map(|line| {
            let len = line.len() + 1;
            let byte_offset = line_start + current_len;
            line_start += len;
            Span { byte_offset, len }
        });

        let orig_line_num = self.lines.len();
        self.lines.extend(lines);
        let new_line_num = self.lines.len();

        self.sources
            .push((name.into(), orig_line_num..new_line_num));

        self.sources.len() - 1
    }

    /// Get the complete content of the source map, including all sources one after the other.
    pub fn content(&self) -> &str {
        &self.content
    }

    /// Get the portion of the source covered by the given [`Span`].
    ///
    /// This method may return `None` if the span extends beyond the current content of the source
    /// map, or if either endpoint of the span splits a multi-byte UTF-8 character. Spans obtained
    /// from methods on this source map, or from [`Source`]s or [`Line`]s of this source map, are
    /// guaranteed to be valid.
    pub fn span(&self, span: Span) -> Option<&str> {
        self.content.get(span.range())
    }

    /// Non-panicking version of [`SourceMap::source`].
    pub fn source_checked(&self, index: usize) -> Option<Source> {
        let (_, range) = self.source_info(index)?;

        let first_line_index = range.start;
        let lines = &self.lines[range];
        let start = lines.first().unwrap().start();
        let end = lines.last().unwrap().end();
        let content = &self.content[start..end];

        Some(Source {
            map: self,
            index,
            lines,
            first_line_index,
            content,
        })
    }

    /// Get the [`Source`] with the given index.
    ///
    /// Sources are indexed from zero, in the order in which they were added to the source map.
    ///
    /// # Panics
    ///
    /// This method will panic if the given index is out of range for the sources currently added
    /// to the source map.
    pub fn source(&self, index: usize) -> Source {
        self.source_checked(index).expect("invalid source index")
    }

    /// An iterator over the [`Source`]s of this source map.
    ///
    /// This iterator yields sources in the same order with which they were added to the source
    /// map.
    pub fn sources(&self) -> Sources {
        Sources {
            map: self,
            range: 0..self.sources.len(),
        }
    }

    /// Non-panicking version of [`SourceMap::global_line`].
    pub fn global_line_checked(&self, index: usize) -> Option<Line> {
        if index >= self.lines.len() {
            return None;
        }

        let source_index = self.index_of_source_containing_global_line(index).unwrap();
        let source = self.source(source_index);

        Some(source.line(index - source.first_line_index))
    }

    /// Get the [`Line`] with the given global index.
    ///
    /// Source lines can be indexed either relative to the source in which they appear, or relative
    /// to the entire source map. This method looks up lines by the latter; to look up lines by the
    /// former, see [`Source::line`].
    pub fn global_line(&self, index: usize) -> Line {
        self.global_line_checked(index)
            .expect("invalid global line index")
    }

    /// An iterator over all of the [`Line`]s in all of the sources in this source map.
    pub fn global_lines(&self) -> SourceLines {
        SourceLines {
            map: self,
            range: 0..self.lines.len(),
        }
    }

    /// Get the [`Location`] of the given global byte offset.
    ///
    /// This method may return `None` if the given byte offset is out of bounds of the source map,
    /// or if it does not correspond to a UTF-8 character boundary.
    pub fn location_of_offset(&self, byte_offset: usize) -> Option<Location> {
        let line_index = self.index_of_global_line_containing_offset(byte_offset)?;
        let line = self.global_line(line_index);

        let line_offset = byte_offset - line.span().byte_offset;
        let column = line
            .content
            .char_indices()
            .position(|(i, _)| i == line_offset)?;

        Some(Location {
            source: line.source.index,
            line: line.index_in_source,
            column,
        })
    }

    /// Get the inclusive start and end [`Location`]s of the given [`Span`].
    pub fn span_extents(&self, span: Span) -> Option<(Location, Location)> {
        let start = self.location_of_offset(span.start())?;
        let end = self.location_of_offset(span.end() - 1)?;
        Some((start, end))
    }
}

/// An iterator over the [`Source`]s of a [`SourceMap`].
///
/// Created via [`SourceMap::sources`]; see that method's documentation for more details.
#[derive(Debug, Clone)]
pub struct Sources<'smap> {
    map: &'smap SourceMap,
    range: Range<usize>,
}

impl<'smap> Iterator for Sources<'smap> {
    type Item = Source<'smap>;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.range.next()?;
        Some(self.map.source(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl DoubleEndedIterator for Sources<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let n = self.range.next_back()?;
        Some(self.map.source(n))
    }
}

impl ExactSizeIterator for Sources<'_> {}

impl FusedIterator for Sources<'_> {}

/// A single source within a [`SourceMap`].
///
/// A source is either a source file or an input on the REPL.
///
/// Methods on [`Source`] that return borrowed data are bound by the lifetime of the owning
/// [`SourceMap`] (`'smap`), not the lifetime of the [`Source`].
#[derive(Debug, Clone, Copy)]
pub struct Source<'smap> {
    map: &'smap SourceMap,
    index: usize,
    lines: &'smap [Span],
    first_line_index: usize,
    content: &'smap str,
}

impl<'smap> Source<'smap> {
    /// Get the name of this source.
    pub fn name(&self) -> &'smap SourceName {
        &self.map.sources[self.index].0
    }

    /// Get the index of this source within the owning [`SourceMap`].
    pub fn index(&self) -> usize {
        self.index
    }

    /// Get the slice of [`Span`]s corresponding to each line of this source.
    pub fn line_spans(&self) -> &'smap [Span] {
        self.lines
    }

    /// Get the entire contents of this source.
    pub fn content(&self) -> &'smap str {
        self.content
    }

    /// Get the number of lines in this source.
    pub fn num_lines(&self) -> usize {
        self.lines.len()
    }

    /// An iterator over the [`Line`]s of this source.
    pub fn lines(&self) -> SourceLines<'smap> {
        SourceLines {
            map: self.map,
            range: self.global_line_range(),
        }
    }

    /// Get the range of global line indices that comprise this source.
    pub fn global_line_range(&self) -> Range<usize> {
        self.first_line_index..self.first_line_index + self.lines.len()
    }

    /// Get the [`Span`] that covers this source's content.
    pub fn span(&self) -> Span {
        let byte_offset = self.lines.first().unwrap().start();
        let end = self.lines.last().unwrap().end();
        let len = end - byte_offset;
        Span { byte_offset, len }
    }

    /// Non-panicking version of [`Source::line`].
    pub fn line_checked(&self, n: usize) -> Option<Line<'smap>> {
        let content = self.lines.get(n).and_then(|span| self.map.span(*span))?;
        Some(Line {
            source: *self,
            index_in_source: n,
            content,
        })
    }

    /// Get the [`Line`] at the given index within this source.
    ///
    /// # Panics
    ///
    /// This will panic if `n` is an invalid index into the lines of this source (i.e. if `n >=
    /// self.num_lines()`).
    pub fn line(&self, n: usize) -> Line<'smap> {
        self.line_checked(n).expect("invalid line index")
    }
}

impl<'smap> AsRef<str> for Source<'smap> {
    fn as_ref(&self) -> &str {
        self.content
    }
}

/// An iterator over the [`Line`]s of a [`Source`].
///
/// Created via the [`Source::lines`] and [`SourceMap::global_lines`].
#[derive(Debug, Clone)]
pub struct SourceLines<'smap> {
    map: &'smap SourceMap,
    range: Range<usize>,
}

impl<'smap> Iterator for SourceLines<'smap> {
    type Item = Line<'smap>;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.range.next()?;
        Some(self.map.global_line(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl<'smap> DoubleEndedIterator for SourceLines<'smap> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let n = self.range.next_back()?;
        Some(self.map.global_line(n))
    }
}

impl<'smap> ExactSizeIterator for SourceLines<'smap> {}

impl<'smap> FusedIterator for SourceLines<'smap> {}

/// A line of a particular [`Source`].
///
/// Methods on [`Line`] that return borrowed data are bound by the lifetime of the owning
/// [`SourceMap`] (`'smap`), not the lifetime of the [`Line`].
#[derive(Debug, Clone, Copy)]
pub struct Line<'smap> {
    source: Source<'smap>,
    index_in_source: usize,
    content: &'smap str,
}

impl<'smap> Line<'smap> {
    /// Get the [`Source`] in which this line appears.
    pub fn source(&self) -> Source<'smap> {
        self.source
    }

    /// Get the line index within this line's [`Source`].
    pub fn index_in_source(&self) -> usize {
        self.index_in_source
    }

    /// Get the full contents of this line.
    ///
    /// Note that lines are always terminated by `'\n'` characters.
    pub fn content(&self) -> &'smap str {
        self.content
    }

    /// Get the [`Span`] covering this line's content.
    pub fn span(&self) -> Span {
        self.source.lines[self.index_in_source]
    }

    /// Get the global index of this line within the [`SourceMap`].
    pub fn global_index(&self) -> usize {
        self.source.first_line_index + self.index_in_source
    }

    /// Get the character at column index `n` within this line.
    ///
    /// This method simply counts to the `n`'th UTF-8 character in the line. This may or may not
    /// correspond with the rendered position of the character in the line, e.g. in the case of
    /// combining diacritics or zero-width characters.
    pub fn column(&self, n: usize) -> Option<char> {
        self.content.chars().nth(n)
    }
}

/// A source code location.
///
/// This represents a particular character within the source code. The character is specified by
/// the source index, the source-relative line index, and column index of the character within a
/// particular [`SourceMap`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    /// The source index.
    pub source: usize,

    /// The line index within the source.
    pub line: usize,

    /// The character index within the line.
    pub column: usize,
}
