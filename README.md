Following along (loosely) with [_Crafting Interpreters_][CI] in Rust.

Going a lot harder on several bits of the design than the book does. In particular, aiming
for much more robust source code representations and error handling/reporting.

I'm currently early on in part 1 of the book. The tree-walking interpreter will live in
[`tlox`](./tlox). When I get to part two (the bytecode interpreter), many components of
that crate (e.g. source maps, error handling, lexical and syntactic structures) will be
separated out into other crates to be shared between the two implementations.

[CI]: https://craftinginterpreters.com/
