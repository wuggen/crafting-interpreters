use super::*;

impl SourceMap {
    fn print_line(&self, i: usize) {
        if let Some(line) = self.global_line_checked(i) {
            eprintln!(
                "note: line {i} ({:?}) {:?}",
                line.span().range(),
                line.content(),
            );
        } else {
            eprintln!("note: no lines");
        }
    }

    fn print_source(&self, i: usize) {
        if let Some(source) = self.source_checked(i) {
            eprintln!(
                "note: source {i}: {} ({:?}) {:?}",
                source.name(),
                source.span().range(),
                source.content(),
            );
        } else {
            eprintln!("note: no sources");
        }
    }
}

#[test]
fn source_indices_and_contents() {
    let map = SourceMap::new();
    assert_eq!(map.add_source(3, "hey"), 0);
    assert_eq!(map.add_source(PathBuf::from("yo"), "lmao"), 1);
    assert_eq!(map.add_source(45, "lol"), 2);

    assert_eq!(&*map.source(0).content(), "hey\n");
    assert_eq!(&*map.source(1).content(), "lmao\n");
    assert_eq!(&*map.source(2).content(), "lol\n");

    assert_eq!(&*map.content(), "hey\nlmao\nlol\n");

    // TODO This silliness with the double vec to avoid referencing a dropped read guard should
    // probably be reconsidered...
    assert_eq!(
        map.sources()
            .map(|s| s.content())
            .collect::<Vec<_>>()
            .iter()
            .map(|c| &**c)
            .collect::<Vec<_>>(),
        &["hey\n", "lmao\n", "lol\n"],
    );

    assert_eq!(
        map.sources()
            .map(|s| s.name())
            .collect::<Vec<_>>()
            .iter()
            .map(|c| &**c)
            .collect::<Vec<_>>(),
        &[
            &SourceName::ReplInput(3),
            &SourceName::File("yo".into()),
            &SourceName::ReplInput(45),
        ],
    );

    assert_eq!(map.sources().map(|s| s.index()).collect::<Vec<_>>(), &[
        0, 1, 2
    ],);

    assert_eq!(map.sources().map(|s| s.span()).collect::<Vec<_>>(), &[
        Span {
            byte_offset: 0,
            len: 4
        },
        Span {
            byte_offset: 4,
            len: 5
        },
        Span {
            byte_offset: 9,
            len: 4
        },
    ],);

    assert_eq!(&*map.source(0).line(0).content(), "hey\n");
    assert!(map.source(0).line_checked(1).is_none());

    assert!(map.source_checked(3).is_none());
}

#[test]
fn global_lines() {
    let map = SourceMap::new();
    map.add_source(0, "line 0\nline 1");
    map.add_source(1, "line 2\n");
    map.add_source(2, "line 3\nline 4\nline 5\n");

    let line0 = map.global_line(0);
    assert_eq!(line0.source().index(), 0);
    assert_eq!(line0.index_in_source(), 0);
    assert_eq!(&*line0.content(), "line 0\n");
    assert_eq!(line0.column(2), Some('n'));

    let line1 = map.global_line(1);
    assert_eq!(line1.source().index(), 0);
    assert_eq!(line1.index_in_source(), 1);
    assert_eq!(&*line1.content(), "line 1\n");
    assert_eq!(line1.column(0), Some('l'));

    let line2 = map.global_line(2);
    assert_eq!(line2.source().index(), 1);
    assert_eq!(line2.index_in_source(), 0);
    assert_eq!(&*line2.content(), "line 2\n");
    assert_eq!(line2.column(5), Some('2'));

    let line3 = map.global_line(3);
    assert_eq!(line3.source().index(), 2);
    assert_eq!(line3.index_in_source(), 0);
    assert_eq!(&*line3.content(), "line 3\n");
    assert_eq!(line3.column(1), Some('i'));

    let line5 = map.global_line(5);
    assert_eq!(line5.source().index(), 2);
    assert_eq!(line5.index_in_source(), 2);
    assert_eq!(&*line5.content(), "line 5\n");
}

#[test]
fn line_iterators() {
    let map = SourceMap::new();
    map.add_source(0, "hey\nthere\nbuddy\nlol\n");
    map.add_source(1, "another!\n");
    map.add_source(2, "hehe\nlmao\n");

    let lines = [
        "hey\n",
        "there\n",
        "buddy\n",
        "lol\n",
        "another!\n",
        "hehe\n",
        "lmao\n",
    ];

    // TODO More double vec silliness
    assert_eq!(
        map.source(0)
            .lines()
            .map(|ln| ln.content())
            .collect::<Vec<_>>()
            .iter()
            .map(|ln| &**ln)
            .collect::<Vec<_>>(),
        &lines[0..4],
    );
    assert_eq!(
        map.source(1)
            .lines()
            .map(|ln| ln.content())
            .collect::<Vec<_>>()
            .iter()
            .map(|ln| &**ln)
            .collect::<Vec<_>>(),
        &lines[4..5],
    );
    assert_eq!(
        map.source(2)
            .lines()
            .map(|ln| ln.content())
            .collect::<Vec<_>>()
            .iter()
            .map(|ln| &**ln)
            .collect::<Vec<_>>(),
        &lines[5..],
    );
    assert_eq!(
        map.global_lines()
            .map(|ln| ln.content())
            .collect::<Vec<_>>()
            .iter()
            .map(|ln| &**ln)
            .collect::<Vec<_>>(),
        &lines,
    );
}

#[test]
fn line_cursors() {
    let map = SourceMap::new();
    map.add_source(0, "hey\nthere");
    map.add_source(1, "lol\nlmao\neven");

    let mut cursor = map.global_line(0).cursor();
    assert_eq!(&*cursor.remaining(), "hey\n");
    assert_eq!(cursor.line().global_index(), 0);
    assert_eq!(cursor.source().index(), 0);
    assert_eq!(cursor.advance(), Some('h'));
    assert_eq!(cursor.peek(), Some('e'));
    assert_eq!(&*cursor.remaining(), "ey\n");
    assert_eq!(cursor.byte_offset(), 1);
    assert_eq!(cursor.char_offset(), 1);
    assert_eq!(cursor.advance(), Some('e'));
    assert_eq!(cursor.advance(), Some('y'));
    assert_eq!(cursor.advance(), Some('\n'));
    assert!(cursor.advance().is_none());

    let mut cursor = map.global_line(2).cursor();
    assert_eq!(&*cursor.remaining(), "lol\n");
    assert_eq!(cursor.line().global_index(), 2);
    assert_eq!(cursor.source().index(), 1);
    assert_eq!(cursor.byte_offset(), 10);
    assert_eq!(cursor.char_offset(), 0);
    assert_eq!(cursor.advance(), Some('l'));
    assert_eq!(cursor.peek(), Some('o'));
}

#[test]
fn source_cursors() {
    let map = SourceMap::new();
    map.add_source(0, "line 0\nline 1");
    map.add_source(1, "line 2\nline 3");

    let mut cursor = map.source(0).cursor();
    assert_eq!(&*cursor.remaining(), "line 0\nline 1\n");
    assert_eq!(cursor.line().global_index(), 0);
    assert_eq!(cursor.source().index(), 0);
    for _ in 0..7 {
        cursor.advance();
    }
    assert_eq!(&*cursor.remaining(), "line 1\n");
    assert_eq!(cursor.line().global_index(), 1);
    assert_eq!(cursor.source().index(), 0);
    assert_eq!(cursor.location(), Location {
        source: 0,
        line: 1,
        column: 0,
    },);

    let mut cursor = map.source(1).cursor();
    assert_eq!(&*cursor.remaining(), "line 2\nline 3\n");
    assert_eq!(cursor.line().global_index(), 2);
    assert_eq!(cursor.source().index(), 1);
    assert_eq!(cursor.location(), Location {
        source: 1,
        line: 0,
        column: 0,
    },);
    for _ in 0..7 {
        cursor.advance();
    }
    assert_eq!(&*cursor.remaining(), "line 3\n");
    assert_eq!(cursor.line().global_index(), 3);
    assert_eq!(cursor.source().index(), 1);
}

impl SourceMap {
    fn assert_lines_contiguous(&self) {
        for (i, pair) in self.inner().lines.windows(2).enumerate() {
            if pair[0].end() != pair[1].start() {
                self.print_line(i);
                self.print_line(i + 1);
                panic!("lines {i} and {} are not contiguous", i + 1);
            }
        }
    }

    fn assert_lines_cover_content(&self) {
        if let Some(span) = self.inner().lines.last() {
            if span.end() != self.inner().content.len() {
                self.print_line(self.inner().lines.len() - 1);
                eprintln!("note: content len {}", self.inner().content.len());
                panic!("line spans do not cover content");
            }
        } else if !self.inner().content.is_empty() {
            panic!("no lines, but content is non-empty");
        }
    }

    fn assert_lines_terminated(&self) {
        for (i, span) in self.inner().lines.iter().enumerate() {
            let content = self.content();
            let c = match content.get(span.end() - 1..span.end()) {
                Some(c) => c,
                None => {
                    self.print_line(i);
                    panic!("line {i}'s final byte is not a valid UTF-8 character");
                }
            };

            if c != "\n" {
                self.print_line(i);
                panic!("line {i} does not end in a newline (actual char {c}");
            }
        }
    }

    fn assert_sources_contiguous(&self) {
        for (i, pair) in self.inner().sources.windows(2).enumerate() {
            if pair[0].1.end != pair[1].1.start {
                self.print_source(i);
                self.print_source(i + 1);
                panic!("sources {i} and {} are not contiguous", i + 1);
            }
        }
    }

    fn assert_sources_cover_content(&self) {
        if let Some((_, range)) = self.inner().sources.last() {
            if range.end != self.inner().lines.len() {
                self.print_source(self.inner().sources.len() - 1);
                eprintln!("note: {} global lines", self.inner().lines.len());
                panic!("source ranges do not cover content");
            }
        } else if !self.inner().content.is_empty() {
            panic!("no sources, but content is non-empty");
        }
    }

    fn assert_invariants(&self) {
        self.assert_lines_contiguous();
        self.assert_lines_cover_content();
        self.assert_lines_terminated();
        self.assert_sources_contiguous();
        self.assert_sources_cover_content();
    }
}

fn invarints_test<S: AsRef<str>>(sources: impl IntoIterator<Item = S>) {
    let map = SourceMap::new();
    for (name, source) in sources.into_iter().enumerate() {
        map.add_source(name, source.as_ref());
    }
    map.assert_invariants();
}

#[test]
fn empty_source_map() {
    invarints_test::<&str>([]);
}

#[test]
fn single_source_one_line() {
    invarints_test(["hey there\n"]);
}

#[test]
fn single_source_one_line_unterminated() {
    invarints_test(["lol hey"]);
}

#[test]
fn single_source_multiple_lines() {
    invarints_test(["lol\n    hey\n"]);
}

#[test]
fn single_source_multiple_lines_unterminated() {
    invarints_test(["line 1\nline 2"]);
}

#[test]
fn two_single_line_sources() {
    invarints_test(["source 1\n", "source 2\n"]);
}

#[test]
fn two_single_line_sources_unterminated() {
    invarints_test(["source 1", "source 2"]);
}

#[test]
fn two_multi_line_sources() {
    invarints_test(["s1 ln1\ns1 ln2\n", "s2 ln1\ns2 ln2\n"]);
}

#[test]
fn two_multi_line_sources_unterminated() {
    invarints_test(["s1 ln1\ns1 ln2", "s2 ln1\ns2 ln2"]);
}

#[test]
fn freeform_sources() {
    invarints_test([
        "lmao hey there",
        "what\nis\nup\nmy\nguy\n",
        r#"if I did
            THIS......
            ..... would that mean anything to you?
"#,
        "heyyyyy one more\n",
    ]);
}
