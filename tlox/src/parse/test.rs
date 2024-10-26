use indoc::indoc;
use insta::assert_snapshot;

use super::Stmt;
use crate::diag::render::render_dcx;
use crate::session::Session;
use crate::util::test::parse_new_source;

#[test]
fn literals() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(key, "true;").unwrap(),
            @r#"
        true;{1:1..1:5}
        "#);
        assert!(render_dcx().is_empty());

        assert_snapshot!(
            parse_new_source(key, "134;").unwrap(),
            @r#"
        134;{1:1..1:4}
        "#);
        assert!(render_dcx().is_empty());

        assert_snapshot!(
            parse_new_source(key, r#""lol hey\ndude";"#).unwrap(),
            @r#"
        "lol hey\ndude";{1:1..1:16}
        "#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn comp_chain() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(
                key,
                indoc! {r#"
                45 < nil >= false
                    <= "wow" > 003.32;
                "#},
            ).unwrap(),
            @r#"
        (((45 < nil) >= false) <= "wow") > 3.32;{1:1..2:22}
        "#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn comp_chain_with_parens() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(key, r#"45 < ("wow" >= nil);"#).unwrap(),
            @r#"
        45 < ("wow" >= nil);{1:1..1:20}
        "#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn lotsa_parens() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(
                key,
                indoc! {r#"
                (((true + "false") - (nil / nil) >= 0 * "hey") % ("what")) + (0);
                "#},
            ).unwrap(),
            @r#"
        ((((true + "false") - (nil / nil)) >= 0 * "hey") % ("what")) + (0);{1:1..1:65}
        "#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn err_missing_lhs() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, "+ 4;");
            render_dcx()
        }, @r#"
        error: unexpected `+` token in input
          --> %i0:1:1
          |
        1 | + 4;
          | ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#);

        assert_snapshot!({
            parse_new_source(key, "4 + (* nil) - 5;");
            render_dcx()
        }, @r#"
        error: unexpected `*` token in input
          --> %i0:1:6
          |
        1 | 4 + (* nil) - 5;
          |      ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#);
    });
}

#[test]
fn err_missing_rhs() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, "4 +;");
            render_dcx()
        }, @r#"
        error: statement terminated prematurely
          --> %i0:1:4
          |
        1 | 4 +;
          |    ^ statement terminated here

        "#);
    });
}

#[test]
fn err_early_close_paren() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, "4 + (nil *) - 5;");
            render_dcx()
        }, @r#"
        error: parentheses closed prematurely
          --> %i0:1:11
          |
        1 | 4 + (nil *) - 5;
          |     -     ^ parentheses closed here
          |     |      
          |     parentheses opened here

        "#);
    });
}

#[test]
fn err_unclosed_paren() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, r#""hey" + (4 - nil"#);
            render_dcx()
        }, @r#"
        error: unclosed parentheses
          --> %i0:1:17
          |
        1 | "hey" + (4 - nil
          |         -       ^ expected `)` here
          |         |       
          |         parentheses opened here

        "#);

        assert_snapshot!({
            parse_new_source(
                key,
                indoc! {r#"
                123.4 - (nil



                "whoops";"#},
            );
            render_dcx()
        }, @r#"
        error: unclosed parentheses
          --> %i0:5:1
          |
        1 | 123.4 - (nil
          |         - parentheses opened here
          .
        5 | "whoops";
          | ^^^^^^^^ expected `)` here

        "#);
    });
}

#[test]
fn err_two_ops() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, "8 * + 4");
            render_dcx()
        }, @r#"
        error: unexpected `+` token in input
          --> %i0:1:5
          |
        1 | 8 * + 4
          |     ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#);
    })
}

#[test]
fn err_multiple() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(key, "8 * + (4 - ) / (  ) + 5");
            render_dcx()
        }, @r#"
        error: unexpected `+` token in input
          --> %i0:1:5
          |
        1 | 8 * + (4 - ) / (  ) + 5
          |     ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#);

        assert_snapshot!({
            parse_new_source(
                key,
                indoc! {r#"
                / false * (nil
                    - ) == ()
                "#},
            );
            render_dcx()
        }, @r#"
        error: unexpected `/` token in input
          --> %i0:1:1
          |
        1 | / false * (nil
          | ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

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
        assert_snapshot!({
            parse_new_source(key, "45 - nil ) / false");
            render_dcx()
        }, @r#"
        error: unterminated statement
          --> %i0:1:10
          |
        1 | 45 - nil ) / false
          | -------- ^ expected semicolon here
          | |         
          | this statement

        error: unexpected `)` token in input
          --> %i0:1:10
          |
        1 | 45 - nil ) / false
          |          ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#);
    });
}

#[test]
fn expr_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(key, "4 + 5; false - true;").unwrap(),
            @r#"
        4 + 5;{1:1..1:6}
        false - true;{1:8..1:20}
        "#
        );
        assert!(render_dcx().is_empty());
    })
}

#[test]
fn print_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(key, "print 4; print false;").unwrap(),
            @r#"
            print 4;{1:1..1:8}
            print false;{1:10..1:21}
            "#
        );
        assert!(render_dcx().is_empty())
    })
}

#[test]
fn err_multiple_stmts() {
    Session::with_default(|key| {
        assert_snapshot!({
            parse_new_source(
                key,
                indoc! {r#"
                8 /;
                print;
                false * ();
                print "heya lol"; // this one should be fine
                48 print +0;
                "#},
            );
            render_dcx()
        }, @r#"
        error: statement terminated prematurely
          --> %i0:1:4
          |
        1 | 8 /;
          |    ^ statement terminated here

        error: statement terminated prematurely
          --> %i0:2:6
          |
        2 | print;
          |      ^ statement terminated here

        error: parentheses closed prematurely
          --> %i0:3:10
          |
        3 | false * ();
          |         -^ parentheses closed here
          |         | 
          |         parentheses opened here

        error: unterminated statement
          --> %i0:5:4
          |
        5 | 48 print +0;
          | -- ^^^^^ expected semicolon here
          | |   
          | this statement

        error: unexpected `+` token in input
          --> %i0:5:10
          |
        5 | 48 print +0;
          |          ^ unexpected token here
          |
          = note: expected number, string, `true`, `false`, `nil`, or `(`

        "#
        );
    })
}

#[test]
fn decl_stmts() {
    Session::with_default(|key| {
        assert_snapshot!(
            parse_new_source(
                key,
                indoc! {r#"
                var a;
                var b = a + 4;
                "#},
            ).unwrap(),
            @r#"
        var a;{1:1..1:6}
        var b = a + 4;{2:1..2:14}
        "#,
        );

        assert_snapshot!(
            parse_new_source(
                key,
                indoc! {r#"
                var hey_there = "lol";
                print hey_there;
                var x = y;
                "#}
            ).unwrap(),
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
            {
                parse_new_source(key, "var = 4 + 4;");
                render_dcx()
            },
            @r#"
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
            {
                parse_new_source(key, "var lol = ;");
                render_dcx()
            },
            @r#"
        error: statement terminated prematurely
          --> %i0:1:11
          |
        1 | var lol = ;
          |           ^ statement terminated here

        "#,
        );

        assert_snapshot!(
            {
                parse_new_source(key, "var lmao = no");
                render_dcx()
            },
            @r#"
        error: unterminated statement
          --> %i0:1:14
          |
        1 | var lmao = no
          | -------------^ expected semicolon here
          | |            
          | this statement

        "#,
        );

        assert_snapshot!(
            {
                parse_new_source(key, "var = ");
                render_dcx()
            },
            @r#"
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
