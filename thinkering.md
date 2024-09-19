# Error rendering

## Diagnostic contents

- A main error/warning message
- A primary span with label
- A set of secondary spans with labels
- A set of additional notes
- A set of sub-diagnostics? Maybe

Sub-diagnostics would be mainly useful for displaying relevant spans in other sources.
Could _maybe_ deal with that from the primary diagnostic?

We'll deal with that later. For now, single-source diagnostics.

## Examples

### Only primary one-line span

```
error: shit's fucked
 ==> some_file.lx:5:8
  |
5 | here's soem code
  |        ^^^^ you done goofed
  |
note: what the hell man
```

### Only primary multi-line span

```
warning: what?
 ==> Input %i4:3:6
  |
3 |   haha and
  | _______^
  | |
4 | |     then
5 | |   what?
  | |______^ c'mon
```

### Multiple one-line spans

```
error: wrong
  ==> broken.lx:13:6
   |
13 | lmao rofl and
   |      ^^^^ incorrect
   |
14 | so forth
   |    ----- fucked up
```

```
error: nope
 ==> hahaha.lx:2:15
  |
2 | okay but what if I didn't
  |      ---      ^^ ????
  |      |
  |      lol really?
  |
note: pointing and laughing
```

### Overlapping one-line spans

```
error: rofl
 ==> something.lx
  |
4 | now { really }
  |     ^^------^^ lmao
  |       |
  |       this done broke it
```

```
warning: another
 ==> a_thing.lx
  |
7 | okay but !then
  |          ^---- out of order??
  |          |
  |          lol
```

```
error: woag
 ==> waow.lx
  |
6 | one word two word lol look at me
  |     ^^^^----      --- huh?
  |     |   |
  |     |   lmao what
  |     |
  |     the fuck dude
```

### One-line and multi-line spans

```
error: aaslkjhdfasdl????
  ==> fhhadsa.lx:8:6
   |
 8 |   word { lmao
   | _______^ ---- really man?
   | |
 9 | |     so then;
10 | | }
   | |_^ whole thing's busted
```

```
error: lorem etc.
 ==> gafgafga.lx:3:10
  |
3 |   okay so (then) {
  |        --  ^^^^  -
  | _______|___|_____|
  | |      |   |
  | |      |   nope lmao
  | |      |
  | |      this don't work neither
  | |
4 | |     what now?;
5 | | }
  | |_- really now
  |
note: lol
```

```
warning: did you mean that?
 ==> hohoho.lx:2:9
  |
2 |   alright (now) {
  |   ------- ^     - lmao
  | __|_______|
  | | |
  | | are you fr?
  | |
3 | | lmao }
  | | ---- ^ lol
  | |_|____|
  |   |
  |   c'mon
```

```
warning: lots of multis
 ==> lol.lx
  |
4 |     hey there
  |   __^   -
  | __|_____|
  | | |
5 | | | man!
  | | |_^  - lol
  | |   |  |
  | |___|__|
  |     |
  |     what
```

```
warning: lots of multis
 ==> lol.lx
  |
4 |     hey there
  |   __^   -
  | __|_____|
  | | |
5 | | | man!
  | |___-  ^ lol
  |   |_|__|
  |     |
  |     what
```

```
error: heh
 ==> thingy.lx
  |
1 |   hey
  | __^
  | |
2 | | man what's
  | |___^ -
  |     | |
  | ____|_|
  | |   |
  | |   lol
  | |
3 | | up?
  | |___- huh
```

```
error: heh
 ==> thingy.lx
  |
1 |     hey
  |   __^
  |   |
2 |   | man what's
  | ______- ^ lol
  | | |     |
  | | |_____|
  | |
3 | |   up?
  | |_____- huh
```

## Drawing rules

- One-line spans in lines with no other spans have their labels printed directly next to
  their underlines
- One-line spans on the same line have their labels staircased, highest at the end of the
  line
  - If the rightmost underline is fully overlapped by a more leftward-starting underline,
    its label should be at least one level below the underline level
- Multi-line spans are composed of these elements:
  - Starting endpoint; an underline with no label
  - Backlines; horizontal lines leading back to the margin from the endpoints
  - Margin lines; vertical lines in the margin between endpoints
  - Ending endpoint; an underline with a label
- Backlines attached to endpoints with no underlines preceding them are on the same level
  as the underline; otherwise, they are at least one level below
- Backlines on the same source line are staircased, highest at the beginning of the line
- Margin lines are assigned to in-progress spans in order of start points; nearest to the
  code first
- One-line spans are staircased underneath any backlines for multi-line endpoints _after_
  them in the line
- Ending endpoints are regarded as normal single-line spans for the purposes of label
  placement
- All source line elements are rendered right-to-left in the line; the label etc. lines
  for more leftward elements are drawn over the lines for more rightward ones
  - Use end point for tie-breaking elements that start at the same point
  - When two underlines start at the same point and one is longer than the other, the
    longer one should have its label line (if any) originate in the first column _after_
    the shorter one

### Algorithm

#### Preprocessing
- Collect relevant sources: for each span in the diagnostic, add its source to the set
- Collect relevant source lines:
  - For each single-line span, add that line to the lines for its source
  - For each multi-line span, add the endpoint lines to the lines for its source, as well
    as one line following the start line and one line preceding the end line
  - Record the maximum number of decimal digits in the line numbers for each source (to
    calculate gutter space)
- Decompose multi-line spans into constituent single-line underlines:
  - Label-less starting points
  - Labeled end-points
- Associate single-line spans (including multi-line endpoints) to their corresponding
  source lines, in the following order per line:
  - If two underlines do not overlap, the one appearing more leftward in the line is
    first.
  - If two underlines overlap, order them first by their lengths, then by their ending
    points, and then by the _inverse_ order of their starting points.

    NB: I have no fucking idea if this is actually a valid order lmao

#### Placing
- For each source line:
  - Staircase backlines:
    - If any non-endpoint underlines appear in the line before the first endpoint,
      initialize backline level to 1; otherwise, initialize to 0
    - For each endpoint on the line, from left to right:
      - Assign it the current backline level
      - Increment the backline level
  - Staircase labels:
    - If the final labeled underline in the line ends before any other underline,
      initialize the label level to 1; otherwise, initialize it to 0
    - For each underline (including endpoints) in the line, from right to left:
      - If it is a non-endpoint labeled underline, assign it the current label level and
        increment the label level
      - If it is a labeled endpoint, assign it the current label level and set the label
        level to one greater than the endpoint's backline level
      - If it is an unlabeled endpoint, set the label level to one greater than the
        endpoint's backline level
- Assign margin lines; for each source line (could be integrated into previous loop):
  - For each endpoint in the line from left to right:
    - If it's an ending point, mark its span's margin line level free
    - If it's a starting point, assign its span the lowest free margin line level and mark
      that level as occupied
  - Throughout this loop, make note of the maximum occupied margin line level across the
    source lines for each source

#### Drawing
- Draw primary message
- Draw source windows; for each source:
  - Draw the source name and, if this source contains the primary span, the start
    coordinates of the primary span
  - Draw a buffer line
  - For each rendered line of this source:
    - Draw the source line, with appropriate gutter and margin space
    - Draw buffer lines according to the maximum label/backline level of the line
    - For each annotation on the line, from right to left:
      - Draw underline
      - Draw label line, if any
      - Draw label, if any
      - Draw backline, if any
      - For multi-line start points, draw margin line
- Draw notes
