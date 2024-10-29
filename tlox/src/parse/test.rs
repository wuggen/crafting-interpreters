use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

use indoc::indoc;
use insta::assert_snapshot;

use super::{parse_source, Stmt};
use crate::diag::render::render_dcx;
use crate::session::{Session, SessionKey};
use crate::syn::SynEq;
use crate::util::test::parse_new_source;

fn file_parse_test(path: PathBuf) {
    let name = path.file_name().unwrap().to_str().unwrap();
    let content = fs::read_to_string(&path)
        .inspect_err(|_| eprintln!("error reading {}", path.display()))
        .unwrap();

    if name.starts_with("err_") {
        file_parse_test_err(path, &content);
    } else {
        file_parse_test_success(path, &content);
    }
}

fn file_parse_test_err(path: PathBuf, content: &str) {
    Session::with_default(|key| {
        let idx = key.get().sm.add_source(path, content);
        let name = key.get().sm.source(idx).name().clone();

        parse_source(key, idx).map(|res| panic!("{name} parsed without error:\n{res}"));
        assert!(
            key.get().dcx.has_errors(),
            "dcx has no errors after failing to parse {name}"
        );

        insta::with_settings!({ description => content }, {
            assert_snapshot!(name.to_string(), render_dcx())
        });
    })
}

fn file_parse_test_success(path: PathBuf, content: &str) {
    Session::with_default(|key| {
        let idx = key.get().sm.add_source(path, content);
        let name = key.get().sm.source(idx).name().clone();
        let first_parse = parse_source(key, idx)
            .or_else(|| panic!("failed to parse {name}"))
            .unwrap();

        let first_parse_printed = first_parse.to_string();
        let idx = key
            .get()
            .sm
            .add_source(name.to_string() + "@reparse", &first_parse_printed);
        let reparse = parse_source(key, idx)
            .or_else(|| panic!("failed to reparse {name} after pretty-printing"))
            .unwrap();

        assert!(first_parse.syn_eq(&reparse), "{name} failed reparse check");
        assert!(
            !key.get().dcx.has_errors(),
            "dcx has errors after {name}:\n{}",
            render_dcx()
        );

        insta::with_settings!({ description => content }, {
            assert_snapshot!(name.to_string(), reparse);
        });
    })
}

fn parse_test(key: SessionKey, source: &str) -> String {
    let mut res = String::new();
    if let Some(tree) = parse_new_source(key, source) {
        write!(res, "{tree}").unwrap();
    }

    if key.get().dcx.has_errors() {
        writeln!(res, "\n--> Diagnostics:").unwrap();
        res.push_str(&render_dcx());
    }

    res
}

#[test]
fn literals() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "true;"),
            @r#"
        true;{1:1..1:5}
        "#);

        assert_snapshot!(
            parse_test(key, "134;"),
            @r#"
        134;{1:1..1:4}
        "#);

        assert_snapshot!(
            parse_test(key, r#""lol hey\ndude";"#),
            @r#"
        "lol hey\ndude";{1:1..1:16}
        "#);
    });
}

#[test]
fn comp_chain() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                45 < nil >= false
                    <= "wow" > 003.32;
                "#},
            ),
            @r#"
        (((45 < nil) >= false) <= "wow") > 3.32;{1:1..2:22}
        "#);
    });
}

#[test]
fn comp_chain_with_parens() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, r#"45 < ("wow" >= nil);"#),
            @r#"
        45 < ("wow" >= nil);{1:1..1:20}
        "#);
    });
}

#[test]
fn lotsa_parens() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                (((true + "false") - (nil / nil) >= 0 * "hey") % ("what")) + (0);
                "#},
            ),
            @r#"
        ((((true + "false") - (nil / nil)) >= 0 * "hey") % ("what")) + (0);{1:1..1:65}
        "#);
    });
}

#[test]
fn err_missing_lhs() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "+ 4;"),
            @r#"

        --> Diagnostics:
        error: unexpected `+` token in input
          --> %i0:1:1
          |
        1 | + 4;
          | ^ unexpected token here
          |
          = note: expected statement

        "#);

        assert_snapshot!(
            parse_test(key, "4 + (* nil) - 5;"),
            @r#"

        --> Diagnostics:
        error: unexpected `*` token in input
          --> %i0:1:6
          |
        1 | 4 + (* nil) - 5;
          |      ^ unexpected token here
          |
          = note: expected expression

        "#);
    });
}

#[test]
fn err_missing_rhs() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "4 +;"),
            @r#"

        --> Diagnostics:
        error: statement terminated prematurely
          --> %i0:1:4
          |
        1 | 4 +;
          |    ^ statement terminated here
          |
          = note: expected expression

        "#);
    });
}

#[test]
fn err_early_close_paren() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "4 + (nil *) - 5;"),
            @r#"

        --> Diagnostics:
        error: parentheses closed prematurely
          --> %i0:1:11
          |
        1 | 4 + (nil *) - 5;
          |     -     ^ parentheses closed here
          |     |      
          |     parentheses opened here
          |
          = note: expected expression

        "#);
    });
}

#[test]
fn err_unclosed_paren() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, r#""hey" + (4 - nil"#),
            @r#"

        --> Diagnostics:
        error: unclosed parentheses
          --> %i0:1:17
          |
        1 | "hey" + (4 - nil
          |         -       ^ parentheses should have been closed here
          |         |       
          |         parentheses opened here
          |
          = note: expected `)`

        "#);

        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                123.4 - (nil



                "whoops";"#},
            ),
            @r#"

        --> Diagnostics:
        error: unclosed parentheses
          --> %i0:5:1
          |
        1 | 123.4 - (nil
          |         - parentheses opened here
          .
        5 | "whoops";
          | ^^^^^^^^ parentheses should have been closed here
          |
          = note: expected `)`

        "#);
    });
}

#[test]
fn err_two_ops() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "8 * + 4"),
            @r#"

        --> Diagnostics:
        error: unexpected `+` token in input
          --> %i0:1:5
          |
        1 | 8 * + 4
          |     ^ unexpected token here
          |
          = note: expected expression

        "#);
    })
}

#[test]
fn err_multiple() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "8 * + (4 - ) / (  ) + 5"),
            @r#"

        --> Diagnostics:
        error: unexpected `+` token in input
          --> %i0:1:5
          |
        1 | 8 * + (4 - ) / (  ) + 5
          |     ^ unexpected token here
          |
          = note: expected expression

        "#);

        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                / false * (nil
                    - ) == ()
                "#},
            ),
            @r#"

        --> Diagnostics:
        error: unexpected `/` token in input
          --> %i0:1:1
          |
        1 | / false * (nil
          | ^ unexpected token here
          |
          = note: expected statement

        "#);
    });
}

/// Spans for parenthesized expressions should include the parentheses.
#[test]
fn paren_spans() {
    Session::with_default(|key| {
        let program = parse_new_source(key, "(4 + 10);").unwrap();
        match &program.stmts[0].node {
            Stmt::Expr { val } => assert_eq!(val.span.range(), 0..8),
            stmt => panic!("should have parsed to expression statement, got {stmt:?} instead"),
        }
    })
}

#[test]
fn err_spurious_close_paren() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "45 - nil ) / false"),
             @r#"

        --> Diagnostics:
        error: unterminated statement
          --> %i0:1:10
          |
        1 | 45 - nil ) / false
          | -------- ^ statement should have been terminated here
          | |         
          | this statement
          |
          = note: expected `;`

        error: unexpected `)` token in input
          --> %i0:1:10
          |
        1 | 45 - nil ) / false
          |          ^ unexpected token here
          |
          = note: expected statement

        "#);
    });
}

#[test]
fn expr_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "4 + 5; false - true;"),
            @r#"
        4 + 5;{1:1..1:6}
        false - true;{1:8..1:20}
        "#
        );
    })
}

#[test]
fn print_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "print 4; print false;"),
            @r#"
            print 4;{1:1..1:8}
            print false;{1:10..1:21}
            "#
        );
    })
}

#[test]
fn err_multiple_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                8 /;
                print;
                false * ();
                print "heya lol"; // this one should be fine
                48 print +0;
                "#},
            ),
            @r#"

        --> Diagnostics:
        error: statement terminated prematurely
          --> %i0:1:4
          |
        1 | 8 /;
          |    ^ statement terminated here
          |
          = note: expected expression

        error: statement terminated prematurely
          --> %i0:2:6
          |
        2 | print;
          |      ^ statement terminated here
          |
          = note: expected expression

        error: parentheses closed prematurely
          --> %i0:3:10
          |
        3 | false * ();
          |         -^ parentheses closed here
          |         | 
          |         parentheses opened here
          |
          = note: expected expression

        error: unterminated statement
          --> %i0:5:4
          |
        5 | 48 print +0;
          | -- ^^^^^ statement should have been terminated here
          | |   
          | this statement
          |
          = note: expected `;`

        error: unexpected `+` token in input
          --> %i0:5:10
          |
        5 | 48 print +0;
          |          ^ unexpected token here
          |
          = note: expected expression

        "#
        );
    })
}

#[test]
fn decl_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                var a;
                var b = a + 4;
                "#},
            ),
            @r#"
        var a;{1:1..1:6}
        var b = a + 4;{2:1..2:14}
        "#,
        );

        assert_snapshot!(
            parse_test(
                key,
                indoc! {r#"
                var hey_there = "lol";
                print hey_there;
                var x = y;
                "#}
            ),
            @r#"
        var hey_there = "lol";{1:1..1:22}
        print hey_there;{2:1..2:16}
        var x = y;{3:1..3:10}
        "#,
        );
    })
}

#[test]
fn err_decl_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "var = 4 + 4;"),
            @r#"

        --> Diagnostics:
        error: missing name in variable declaration
          --> %i0:1:5
          |
        1 | var = 4 + 4;
          | --- ^ expected variable name here
          | |    
          | declaration requires a variable name
          |
          = note: expected identifier

        "#,
        );

        assert_snapshot!(
            parse_test(key, "var lol = ;"),
            @r#"

        --> Diagnostics:
        error: statement terminated prematurely
          --> %i0:1:11
          |
        1 | var lol = ;
          |           ^ statement terminated here
          |
          = note: expected expression

        "#,
        );

        assert_snapshot!(
            parse_test(key, "var lmao = no"),
            @r#"

        --> Diagnostics:
        error: unterminated statement
          --> %i0:1:14
          |
        1 | var lmao = no
          | -------------^ statement should have been terminated here
          | |            
          | this statement
          |
          = note: expected `;`

        "#,
        );

        assert_snapshot!(
            parse_test(key, "var = "),
            @r#"

        --> Diagnostics:
        error: missing name in variable declaration
          --> %i0:1:5
          |
        1 | var = 
          | --- ^ expected variable name here
          | |    
          | declaration requires a variable name
          |
          = note: expected identifier

        "#,
        )
    })
}

#[test]
fn assignment_exprs() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "what = 54;"),
            @r#"
        what = 54;{1:1..1:10}
        "#,
        );

        assert_snapshot!(
            parse_test(key, "print (lmao = 4) + 8;"),
            @r#"
        print (lmao = 4) + 8;{1:1..1:21}
        "#,
        );

        assert_snapshot!(
            parse_test(key, "print a = b = c;"),
            @r#"
        print a = b = c;{1:1..1:16}
        "#,
        );

        assert_snapshot!(
            parse_test(key, "var x = y = z;"),
            @r#"
        var x = y = z;{1:1..1:14}
        "#,
        );
    })
}

#[test]
fn err_invalid_place_exprs() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "(a = b) = c;"),
            @r#"

        --> Diagnostics:
        error: invalid place expression on left side of assignment
          --> %i0:1:1
          |
        1 | (a = b) = c;
          | ^^^^^^^ - expected place expression due to assignment here
          | |        
          | invalid place expression
          |
          = note: expected identifier

        "#,
        );

        assert_snapshot!(
            parse_test(key, "7 + 8 = 15;"),
            @r#"

        --> Diagnostics:
        error: invalid place expression on left side of assignment
          --> %i0:1:1
          |
        1 | 7 + 8 = 15;
          | ^^^^^ - expected place expression due to assignment here
          | |      
          | invalid place expression
          |
          = note: expected identifier

        "#,
        );

        assert_snapshot!(
            parse_test(key, "var a = b + c = d;"),
            @r#"

        --> Diagnostics:
        error: invalid place expression on left side of assignment
          --> %i0:1:9
          |
        1 | var a = b + c = d;
          |         ^^^^^ - expected place expression due to assignment here
          |         |      
          |         invalid place expression
          |
          = note: expected identifier

        "#,
        );
    })
}

#[test]
fn block_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "{ var a = 4; print a + 6; }"),
            @r#"
        {
            var a = 4;
            print a + 6;
        }{1:1..1:27}
        "#,
        );

        assert_snapshot!(
            parse_test(key, indoc! {r#"
            {
                a = b;
                {
                    print b;
                    var c;
                }
                print a;
                {}
            }
            "#}),
            @r#"
        {
            a = b;
            {
                print b;
                var c;
            }
            print a;
            {
            }
        }{1:1..9:1}
        "#,
        );
    })
}

#[test]
fn err_block_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "var x = { 4; };"),
            @r#"

        --> Diagnostics:
        error: unexpected `{` token in input
          --> %i0:1:9
          |
        1 | var x = { 4; };
          |         ^ unexpected token here
          |
          = note: expected expression

        "#,
        );

        assert_snapshot!(
            parse_test(key, "{ a; b; c }"),
            @r#"

        --> Diagnostics:
        error: unterminated statement
          --> %i0:1:11
          |
        1 | { a; b; c }
          |         - ^ statement should have been terminated here
          |         |  
          |         this statement
          |
          = note: expected `;`

        "#,
        );

        assert_snapshot!(
            parse_test(key, "{ lol; + 4; }"),
            @r#"

        --> Diagnostics:
        error: unclosed braces
          --> %i0:1:8
          |
        1 | { lol; + 4; }
          | -      ^ braces should have been closed here
          | |       
          | braces opened here
          |
          = note: expected `}`

        error: unexpected `+` token in input
          --> %i0:1:8
          |
        1 | { lol; + 4; }
          |        ^ unexpected token here
          |
          = note: expected statement

        "#,
        );

        assert_snapshot!(
            parse_test(key, "{;}"),
            @r#"

        --> Diagnostics:
        error: unclosed braces
          --> %i0:1:2
          |
        1 | {;}
          | -^ braces should have been closed here
          | | 
          | braces opened here
          |
          = note: expected `}`

        error: unexpected `;` token in input
          --> %i0:1:2
          |
        1 | {;}
          |  ^ unexpected token here
          |
          = note: expected statement

        "#,
        );
    })
}

#[test]
fn if_else_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "if (a == b) lol; else lmao;"),
            @r#"
        if (a == b) lol;
        else lmao;{1:1..1:27}
        "#,
        );

        assert_snapshot!(
            parse_test(key, "if (nope) { print what; } else if (yeah) print lol; else 4;"),
            @r#"
        if (nope) {
            print what;
        }
        else if (yeah) print lol;
        else 4;{1:1..1:59}
        "#,
        );
    })
}

#[test]
fn err_if_else_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_test(key, "if (a == b) lol else lmao; print + 4;"),
            @r#"

        --> Diagnostics:
        error: unterminated statement
          --> %i0:1:17
          |
        1 | if (a == b) lol else lmao; print + 4;
          |             --- ^^^^ statement should have been terminated here
          |             |    
          |             this statement
          |
          = note: expected `;`

        error: unexpected `else` token in input
          --> %i0:1:17
          |
        1 | if (a == b) lol else lmao; print + 4;
          |                 ^^^^ unexpected token here
          |
          = note: expected statement

        error: unexpected `+` token in input
          --> %i0:1:34
          |
        1 | if (a == b) lol else lmao; print + 4;
          |                                  ^ unexpected token here
          |
          = note: expected expression

        "#,
        );

        assert_snapshot!(
            parse_test(key, "if nope { 4 - 1; } print lolol - + 4;"),
            @r#"

        --> Diagnostics:
        error: unexpected identifier token in input
          --> %i0:1:4
          |
        1 | if nope { 4 - 1; } print lolol - + 4;
          |    ^^^^ unexpected token here
          |
          = note: expected `(`

        "#,
        );

        assert_snapshot!(
            parse_test(key, "if (what { print what the; }"),
            @r#"

        --> Diagnostics:
        error: unclosed parentheses
          --> %i0:1:10
          |
        1 | if (what { print what the; }
          |    -     ^ parentheses should have been closed here
          |    |      
          |    parentheses opened here
          |
          = note: expected `)`

        "#,
        );
    })
}
