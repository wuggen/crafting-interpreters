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
use std::ops::{Bound, Range, RangeBounds, Sub};
use std::path::PathBuf;
use std::sync::{MappedRwLockReadGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};

use codespan_reporting::files::{self, Files};

use crate::session::Session;

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

    /// Get the range over which `other` is a subspan of `self`.
    ///
    /// Returns `None` if `self` is not wholly contained within `other`.
    pub fn range_within(&self, other: Span) -> Option<Range<usize>> {
        if other.start() > self.start() || other.end() < self.end() {
            None
        } else {
            Some(self.start() - other.start()..self.end() - other.start())
        }
    }

    /// Get the subspan of `self` covering the given span-relative range.
    pub fn subspan<I: RangeBounds<usize>>(&self, range: I) -> Option<Span> {
        let start = match range.start_bound() {
            Bound::Included(&i) => i,
            Bound::Excluded(&i) => i + 1,
            Bound::Unbounded => 0,
        };

        if start >= self.len {
            return None;
        }

        let end = match range.end_bound() {
            Bound::Included(&j) => j + 1,
            Bound::Excluded(&j) => j,
            Bound::Unbounded => self.len,
        };

        let len = end - start;
        if len > self.end() - start {
            return None;
        }

        Some(Span {
            byte_offset: self.byte_offset + start,
            len,
        })
    }

    /// Join two spans into one.
    ///
    /// This returns the smallest span that covers both of the given spans.
    pub fn join(self, other: Span) -> Span {
        let byte_offset = self.start().min(other.start());
        let end = self.end().max(other.end());
        let len = end - byte_offset;
        Span { byte_offset, len }
    }
}

/// An item with an associated span.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Spanned<T> {
    pub node: T,
    pub span: Span,
}

impl<T: Display> Display for Spanned<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if Session::has_current() {
            Session::with_current(|key| {
                if let Some((start, end)) = key.get().sm.span_extents(self.span) {
                    write!(
                        f,
                        "{}{{{}:{}..{}:{}}}",
                        self.node,
                        start.line + 1,
                        start.column + 1,
                        end.line + 1,
                        end.column + 1,
                    )
                } else {
                    write!(f, "{}{{!!}}", self.node)
                }
            })
        } else {
            write!(f, "{}{{{:?}}}", self.node, self.span.range())
        }
    }
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
    inner: RwLock<SourceMapInner>,
}

#[derive(Debug, Default)]
struct SourceMapInner {
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
    fn inner(&self) -> RwLockReadGuard<SourceMapInner> {
        self.inner.read().unwrap()
    }

    fn inner_mut(&self) -> RwLockWriteGuard<SourceMapInner> {
        self.inner.write().unwrap()
    }

    fn map_inner<T: ?Sized>(
        &self,
        f: impl FnOnce(&SourceMapInner) -> &T,
    ) -> MappedRwLockReadGuard<T> {
        RwLockReadGuard::map(self.inner(), f)
    }

    fn try_map_inner<T: ?Sized>(
        &self,
        f: impl FnOnce(&SourceMapInner) -> Option<&T>,
    ) -> Option<MappedRwLockReadGuard<T>> {
        RwLockReadGuard::try_map(self.inner(), f).ok()
    }

    fn source_info(
        &self,
        source: usize,
    ) -> Option<MappedRwLockReadGuard<(SourceName, Range<usize>)>> {
        self.try_map_inner(|inner| inner.sources.get(source))
    }

    /// Find the global index of the line containing the given byte offset.
    ///
    /// This method operates via binary search on the line spans.
    fn index_of_global_line_containing_offset(&self, byte_offset: usize) -> Option<usize> {
        self.inner()
            .lines
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
        self.inner()
            .sources
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
    pub fn add_source(&self, name: impl Into<SourceName>, content: &str) -> usize {
        let mut inner = self.inner_mut();
        let current_len = inner.content.len();

        inner.content.push_str(content);
        if content.get(content.len() - 1..) != Some("\n") {
            inner.content.push('\n');
        }

        let mut line_start = 0;
        let lines = content.lines().map(|line| {
            let len = line.len() + 1;
            let byte_offset = line_start + current_len;
            line_start += len;
            Span { byte_offset, len }
        });

        let orig_line_num = inner.lines.len();
        inner.lines.extend(lines);
        let new_line_num = inner.lines.len();

        inner
            .sources
            .push((name.into(), orig_line_num..new_line_num));

        inner.sources.len() - 1
    }

    /// Get the complete content of the source map, including all sources one after the other.
    pub fn content(&self) -> MappedRwLockReadGuard<'_, str> {
        self.map_inner(|inner| inner.content.as_str())
    }

    /// Get the portion of the source covered by the given [`Span`].
    ///
    /// This method may return `None` if the span extends beyond the current content of the source
    /// map, or if either endpoint of the span splits a multi-byte UTF-8 character. Spans obtained
    /// from methods on this source map, or from [`Source`]s or [`Line`]s of this source map, are
    /// guaranteed to be valid.
    pub fn span_content(&self, span: Span) -> Option<MappedRwLockReadGuard<'_, str>> {
        self.try_map_inner(|inner| inner.content.get(span.range()))
    }

    /// Gets the [`Source`] containing this span.
    ///
    /// Returns `None` if the span is not wholly contained within a single source.
    pub fn span_source(&self, span: Span) -> Option<Source> {
        let start_line_idx = self.index_of_global_line_containing_offset(span.start())?;
        let end_line_idx = self.index_of_global_line_containing_offset(span.end() - 1)?;

        let start_line = self.global_line(start_line_idx);
        let end_line = self.global_line(end_line_idx);

        if start_line.source().index() != end_line.source().index() {
            None
        } else {
            Some(start_line.source())
        }
    }

    /// Get a cursor over the entire source map.
    pub fn cursor(&self) -> Cursor {
        Cursor {
            map: self,
            offset: 0,
            char_offset: 0,
            range: 0..self.inner().content.len(),
        }
    }

    /// Non-panicking version of [`SourceMap::source`].
    pub fn source_checked(&self, index: usize) -> Option<Source> {
        let (_, range) = &*self.source_info(index)?;
        let lines = (range.start, range.end);

        Some(Source {
            map: self,
            index,
            lines,
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
            range: 0..self.inner().sources.len(),
        }
    }

    /// Non-panicking version of [`SourceMap::global_line`].
    pub fn global_line_checked(&self, index: usize) -> Option<Line> {
        if index >= self.inner().lines.len() {
            return None;
        }

        let source_index = self.index_of_source_containing_global_line(index).unwrap();
        let source = self.source(source_index);

        Some(source.line(index - source.lines.0))
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
            range: 0..self.inner().lines.len(),
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
            .content()
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
pub struct Sources<'sm> {
    map: &'sm SourceMap,
    range: Range<usize>,
}

impl<'sm> Iterator for Sources<'sm> {
    type Item = Source<'sm>;

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
/// [`SourceMap`] (`'sm`), not the lifetime of the [`Source`].
#[derive(Debug, Clone, Copy)]
pub struct Source<'sm> {
    map: &'sm SourceMap,
    index: usize,
    lines: (usize, usize),
}

impl<'sm> Source<'sm> {
    /// Get the source map to which this source belongs.
    pub fn map(&self) -> &'sm SourceMap {
        self.map
    }

    /// Get the name of this source.
    pub fn name(&self) -> MappedRwLockReadGuard<'sm, SourceName> {
        self.map.map_inner(|inner| &inner.sources[self.index].0)
    }

    /// Get the index of this source within the owning [`SourceMap`].
    pub fn index(&self) -> usize {
        self.index
    }

    /// Get the slice of [`Span`]s corresponding to each line of this source.
    pub fn line_spans(&self) -> MappedRwLockReadGuard<'sm, [Span]> {
        self.map
            .map_inner(|inner| &inner.lines[self.global_line_range()])
    }

    /// Get the [`Span`] covering this source.
    pub fn span(&self) -> Span {
        let inner = self.map.inner();
        inner.lines[self.lines.0].join(inner.lines[self.lines.1 - 1])
    }

    /// Get the entire contents of this source.
    pub fn content(&self) -> MappedRwLockReadGuard<'sm, str> {
        self.map.span_content(self.span()).unwrap()
    }

    /// Get a cursor over this source.
    pub fn cursor(&self) -> Cursor<'sm> {
        let span = self.span();
        Cursor {
            map: self.map,
            offset: span.byte_offset,
            char_offset: 0,
            range: span.range(),
        }
    }

    /// Get the number of lines in this source.
    pub fn num_lines(&self) -> usize {
        self.lines.1 - self.lines.0
    }

    /// An iterator over the [`Line`]s of this source.
    pub fn lines(&self) -> SourceLines<'sm> {
        SourceLines {
            map: self.map,
            range: self.global_line_range(),
        }
    }

    /// Get the range of global line indices that comprise this source.
    pub fn global_line_range(&self) -> Range<usize> {
        self.lines.0..self.lines.1
    }

    /// Non-panicking version of [`Source::line`].
    pub fn line_checked(&self, n: usize) -> Option<Line<'sm>> {
        if n < self.num_lines() {
            Some(Line {
                source: *self,
                index_in_source: n,
            })
        } else {
            None
        }
    }

    /// Get the [`Line`] at the given index within this source.
    ///
    /// # Panics
    ///
    /// This will panic if `n` is an invalid index into the lines of this source (i.e. if `n >=
    /// self.num_lines()`).
    pub fn line(&self, n: usize) -> Line<'sm> {
        self.line_checked(n).expect("invalid line index")
    }

    /// Get the span covering the given range of bytes within this source.
    ///
    /// Returns `None` if the given range is outside the bounds of this source, or if it would
    /// split a multibyte character.
    pub fn span_within<I: RangeBounds<usize>>(&self, range: I) -> Option<Span> {
        let span = self.span().subspan(range)?;
        if self.map.span_content(span).is_some() {
            Some(span)
        } else {
            None
        }
    }
}

/// An iterator over the [`Line`]s of a [`Source`].
///
/// Created via the [`Source::lines`] and [`SourceMap::global_lines`].
#[derive(Debug, Clone)]
pub struct SourceLines<'sm> {
    map: &'sm SourceMap,
    range: Range<usize>,
}

impl<'sm> Iterator for SourceLines<'sm> {
    type Item = Line<'sm>;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.range.next()?;
        Some(self.map.global_line(n))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.range.size_hint()
    }
}

impl DoubleEndedIterator for SourceLines<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let n = self.range.next_back()?;
        Some(self.map.global_line(n))
    }
}

impl ExactSizeIterator for SourceLines<'_> {}

impl FusedIterator for SourceLines<'_> {}

/// A line of a particular [`Source`].
///
/// Methods on [`Line`] that return borrowed data are bound by the lifetime of the owning
/// [`SourceMap`] (`'sm`), not the lifetime of the [`Line`].
#[derive(Debug, Clone, Copy)]
pub struct Line<'sm> {
    source: Source<'sm>,
    index_in_source: usize,
}

impl<'sm> Line<'sm> {
    /// Get the source map to which this line belongs.
    pub fn map(&self) -> &'sm SourceMap {
        self.source.map
    }

    /// Get the [`Source`] in which this line appears.
    pub fn source(&self) -> Source<'sm> {
        self.source
    }

    /// Get the line index within this line's [`Source`].
    pub fn index_in_source(&self) -> usize {
        self.index_in_source
    }

    /// Get the full contents of this line.
    ///
    /// Note that lines are always terminated by `'\n'` characters.
    pub fn content(&self) -> MappedRwLockReadGuard<'sm, str> {
        self.map().span_content(self.span()).unwrap()
    }

    /// Get a cursor over this line.
    pub fn cursor(&self) -> Cursor<'sm> {
        let span = self.span();
        Cursor {
            map: self.source.map,
            offset: span.byte_offset,
            char_offset: 0,
            range: span.range(),
        }
    }

    /// Get the [`Span`] covering this line's content.
    pub fn span(&self) -> Span {
        self.source.line_spans()[self.index_in_source]
    }

    /// Get the global index of this line within the [`SourceMap`].
    pub fn global_index(&self) -> usize {
        self.source.lines.0 + self.index_in_source
    }

    /// Get the character at column index `n` within this line.
    ///
    /// This method simply counts to the `n`'th UTF-8 character in the line. This may or may not
    /// correspond with the rendered position of the character in the line, e.g. in the case of
    /// combining diacritics or zero-width characters.
    pub fn column(&self, n: usize) -> Option<char> {
        self.content().chars().nth(n)
    }

    /// Get the span covering the given range of bytes within this line.
    ///
    /// Returns `None` if the range is outside the bounds of this line, or if it would split a
    /// multi-byte character.
    pub fn span_within<I: RangeBounds<usize>>(&self, range: I) -> Option<Span> {
        let span = self.span().subspan(range)?;
        if self.map().span_content(span).is_some() {
            Some(span)
        } else {
            None
        }
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

/// An advancable cursor over the characters of some range of a source map.
#[derive(Debug, Clone)]
pub struct Cursor<'sm> {
    map: &'sm SourceMap,
    offset: usize,
    char_offset: usize,
    range: Range<usize>,
}

impl<'sm> Cursor<'sm> {
    /// Advance the cursor one character.
    ///
    /// Returns the advanced-over character, or `None` if the cursor is at the end of its range.
    pub fn advance(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.offset += c.len_utf8();
        self.char_offset += 1;
        Some(c)
    }

    /// Retract the cursor one character.
    ///
    /// Returns the retracted character, or `None` if the cursor is at the beginning of its range.
    pub fn retract(&mut self) -> Option<char> {
        if self.offset <= self.range.start {
            None
        } else {
            let content = self.map.content();
            self.offset = content.floor_char_boundary(self.offset - 1);
            self.peek()
        }
    }

    /// Get the next character at the cursor, without advancing the cursor.
    ///
    /// Returns `None` if the cursor is at the end of its range.
    pub fn peek(&self) -> Option<char> {
        self.remaining().chars().next()
    }

    /// Get the current global byte offset of the cursor within the source map.
    pub fn byte_offset(&self) -> usize {
        self.offset
    }

    /// Get the current character offset of the cursor within its range.
    pub fn char_offset(&self) -> usize {
        self.char_offset
    }

    /// Create a span starting from the given cursor and ending at this one.
    pub fn span_from(&self, other: &Self) -> Option<Span> {
        if other.offset <= self.offset {
            Some(Span {
                byte_offset: other.offset,
                len: self.offset - other.offset,
            })
        } else {
            None
        }
    }

    /// Get the [`Source`] containing the current cursor location.
    pub fn source(&self) -> Source<'sm> {
        self.map.source(self.source_index())
    }

    /// Get the [`Line`] containing the current cursor location.
    pub fn line(&self) -> Line<'sm> {
        self.map.global_line(self.global_line_index())
    }

    /// Get the string slice from the current cursor location to the end of its range.
    pub fn remaining(&self) -> MappedRwLockReadGuard<'sm, str> {
        MappedRwLockReadGuard::map(self.map.content(), |content| {
            &content[self.offset..self.range.end]
        })
    }

    /// Get the current `Location` of the cursor.
    pub fn location(&self) -> Location {
        self.map.location_of_offset(self.offset).unwrap()
    }
}

impl Cursor<'_> {
    fn global_line_index(&self) -> usize {
        self.map
            .index_of_global_line_containing_offset(self.offset)
            .unwrap()
    }

    fn source_index(&self) -> usize {
        self.map
            .index_of_source_containing_global_line(self.global_line_index())
            .unwrap()
    }
}

impl Sub for &Cursor<'_> {
    type Output = Span;

    fn sub(self, rhs: Self) -> Self::Output {
        self.span_from(rhs).unwrap()
    }
}

#[doc(hidden)]
pub struct MappedAsRef<'a, T: ?Sized> {
    pub mapped: MappedRwLockReadGuard<'a, T>,
}

impl<T: ?Sized> AsRef<T> for MappedAsRef<'_, T> {
    fn as_ref(&self) -> &T {
        &self.mapped
    }
}

impl<'sm> Files<'sm> for SourceMap {
    type FileId = usize;

    type Name = MappedRwLockReadGuard<'sm, SourceName>;

    type Source = MappedAsRef<'sm, str>;

    fn name(&'sm self, id: Self::FileId) -> Result<Self::Name, files::Error> {
        self.source_checked(id)
            .map(|s| s.name())
            .ok_or(files::Error::FileMissing)
    }

    fn source(&'sm self, id: Self::FileId) -> Result<Self::Source, files::Error> {
        self.source_checked(id)
            .map(|s| MappedAsRef {
                mapped: s.content(),
            })
            .ok_or(files::Error::FileMissing)
    }

    fn line_index(&'sm self, id: Self::FileId, byte_index: usize) -> Result<usize, files::Error> {
        let source = self.source_checked(id).ok_or(files::Error::FileMissing)?;
        let source_offset = source.span().byte_offset;
        let global_line_idx = if let Some(idx) =
            self.index_of_global_line_containing_offset(source_offset + byte_index)
        {
            idx
        } else {
            return Ok(source.num_lines() - 1);
        };

        let line = self.global_line(global_line_idx);
        if line.source().index() != id {
            Ok(source.num_lines() - 1)
        } else {
            Ok(line.index_in_source())
        }
    }

    fn line_range(
        &'sm self,
        id: Self::FileId,
        line_index: usize,
    ) -> Result<Range<usize>, files::Error> {
        self.source_checked(id)
            .ok_or(files::Error::FileMissing)
            .and_then(|s| {
                s.line_checked(line_index)
                    .ok_or_else(|| files::Error::LineTooLarge {
                        given: line_index,
                        max: s.num_lines() - 1,
                    })
            })
            .map(|line| {
                let mut span = line.span();
                span.byte_offset -= line.source().span().byte_offset;
                span.range()
            })
    }
}
