Following along (loosely) with [_Crafting Interpreters_][CI] in Rust.

Going a lot harder on several bits of the design than the book does. In
particular, aiming for much more robust source code representations and error
handling/reporting.

I'm currently in part 1 of the book. The tree-walking interpreter will live
in [`tlox`](./tlox). When I get to part two (the bytecode interpreter),
many components of that crate (e.g. source maps, error handling, lexical and
syntactic structures) will be separated out into other crates to be shared
between the two implementations.

# Digressions from the Lox language as specified in the book

I have committed the cardinal sin of diverging from the language spec. In my
defense, no one will ever use this interpreter.

## Use of shadowed variables in initializers

The book's Lox allows this:

```
var a = 4;
var a = a + 5; // a is set to 9
```

but disallows this:

```
{
  var a = 4;
  var a = a + 5; // Error: cannot reference `a` in its own initializer
}
```

This is displeasing to me for two reasons:

- It's an arbitrary inconsistency between the treatment of global vs. local
  variables. Code in the global scope is special-cased in several cases,
  to facilitate use of the language in an interactive prompt, but minimizing
  these discrepancies seems desirable, and this discrepancy in particular seems
  especially arbitrary.
- Forbidding references within variable initializers to variables of the
  same name is counter to my intuition of both how variable declaration and
  initialization should work and to how variable shadowing should work. The
  variable should not exist until its initial value is evaluated, and thus any
  previously-declared variables of the same name should be available for use
  within that initial value.

Granted, in a dynamically typed language, variable shadowing is of marginal
use and is _mostly_ equivalent to reassigning a variable (though lexical
scoping rules do make shadowing useful in certain circumstances even in this
setting). The no-shadowed-variables-in-initializers rule would also mirror the
way _function_ declarations operate (the function is declared and exists to be
referenced recursively within the body of the function), but I think there is
a difference in kind here that justifies the discrepancy; variable initializers
are evaluated _immediately and eagerly,_ while function bodies are evaluated
_lazily when called,_ which makes recursive functions both sensical and useful,
while recursive variables are nonsensical, and the syntax that would produce
one is more usefully construed to do something else so long as a natural
"something else" exists.

So, this version of Lox allows the use of same-name variables in initializers,
in all cases, including in local scopes.

[CI]: https://craftinginterpreters.com/
