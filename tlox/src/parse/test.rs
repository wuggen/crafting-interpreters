use indoc::indoc;
use insta::assert_snapshot;

use crate::context::with_new_interpreter;
use crate::diag::render::render_dcx;
use crate::span::SourceMap;

use super::*;

fn parse_source(source: &str) -> Option<Spanned<Expr>> {
    let source_idx = SourceMap::with_current_mut(|sm| sm.add_source(0, source));

    SourceMap::with_current(|sm| {
        let lexer = Lexer::new(sm.source(source_idx));
        let parser = Parser::new(lexer);
        let res = parser.parse();
        if let Some(res) = res.as_ref() {
            debug_println!("PARSED: {res}\n");
        } else {
            debug_println!("PARSED: None\n");
        }

        res
    })
}

#[test]
fn literals() {
    with_new_interpreter(|_| {
        let res = parse_source("true");
        assert_snapshot!(res.unwrap(), @"true{1:1..1:4}");
        assert!(render_dcx().is_empty());

        let res = parse_source("134");
        assert_snapshot!(res.unwrap(), @"134{1:1..1:3}");
        assert!(render_dcx().is_empty());

        let res = parse_source(r#""lol hey\ndude""#);
        assert_snapshot!(res.unwrap(), @r#""lol hey\ndude"{1:1..1:15}"#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn comp_chain() {
    with_new_interpreter(|_| {
        let res = parse_source(indoc! {r#"
        45 < nil >= false
            <= "wow" > 003.32
        "#});
        assert_snapshot!(res.unwrap().node, @r#"(> (<= (>= (< 45 nil) false) "wow") 3.32)"#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn comp_chain_with_parens() {
    with_new_interpreter(|_| {
        let res = parse_source(r#"45 < ("wow" >= nil)"#);
        assert_snapshot!(res.unwrap().node, @r#"(< 45 (>= "wow" nil))"#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn lotsa_parens() {
    with_new_interpreter(|_| {
        let res = parse_source(indoc! {r#"
        (((true + "false") - (nil / nil) >= 0 * "hey") % ("what")) + (0)
        "#});
        assert_snapshot!(res.unwrap().node, @r#"(+ (% (>= (- (+ true "false") (/ nil nil)) (* 0 "hey")) "what") 0)"#);
        assert!(render_dcx().is_empty());
    });
}

#[test]
fn err_missing_lhs() {
    with_new_interpreter(|_| {
        parse_source("+ 4");
        assert_snapshot!(render_dcx(), @r#"
        error: binary operator without left-hand operand
          --> %i0:1:1
          |
        1 | + 4
          | ^^^ this expression is missing the left-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);

        parse_source("4 + (* nil) - 5");
        assert_snapshot!(render_dcx(), @r#"
        error: binary operator without left-hand operand
          --> %i0:1:6
          |
        1 | 4 + (* nil) - 5
          |      ^^^^^ this expression is missing the left-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);
    });
}

#[test]
fn err_missing_rhs() {
    with_new_interpreter(|_| {
        parse_source("4 +");
        assert_snapshot!(render_dcx(), @r#"
        error: unexpected end of input
          --> %i0:1:4
          |
        1 | 4 +
          |    ^ unexpected token
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);
    });
}

#[test]
fn err_early_close_paren() {
    with_new_interpreter(|_| {
        parse_source("4 + (nil *) - 5");
        assert_snapshot!(render_dcx(), @r#"
        error: binary operator without right-hand operand
          --> %i0:1:11
          |
        1 | 4 + (nil *) - 5
          |      -----^ expected right-hand operand here
          |      |     
          |      this expression is missing the right-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);
    });
}

#[test]
fn err_unclosed_paren() {
    with_new_interpreter(|_| {
        parse_source(r#""hey" + (4 - nil"#);
        assert_snapshot!(render_dcx(), @r#"
        error: unclosed parentheses
          --> %i0:1:17
          |
        1 | "hey" + (4 - nil
          |         -       ^ parentheses should have been closed
          |         |       
          |         parentheses opened here
          |
          = note: expected `)`

        "#);

        parse_source(indoc! {r#"
            123.4 - (nil



            "whoops""#});
        assert_snapshot!(render_dcx(), @r#"
        error: unclosed parentheses
          --> %i0:5:1
          |
        1 | 123.4 - (nil
          |         - parentheses opened here
          .
        5 | "whoops"
          | ^^^^^^^^ parentheses should have been closed
          |
          = note: expected `)`

        "#);
    });
}

#[test]
fn err_multiple() {
    with_new_interpreter(|_| {
        parse_source("8 * + (4 - ) / (  ) + 5");
        assert_snapshot!(render_dcx(), @r#"
        error: binary operator without right-hand operand
          --> %i0:1:12
          |
        1 | 8 * + (4 - ) / (  ) + 5
          |        --- ^ expected right-hand operand here
          |        |    
          |        this expression is missing the right-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        error: parentheses closed prematurely
          --> %i0:1:19
          |
        1 | 8 * + (4 - ) / (  ) + 5
          |                -  ^ parentheses closed here, prematurely
          |                |   
          |                parentheses opened here
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        error: binary operator without left-hand operand
          --> %i0:1:5
          |
        1 | 8 * + (4 - ) / (  ) + 5
          |     ^^^^^^^^^^^^^^^ this expression is missing the left-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);

        parse_source(indoc! {r#"
        / false * (nil
            - ) == ()
        "#});
        assert_snapshot!(render_dcx(), @r#"
        error: binary operator without left-hand operand
          --> %i0:1:1
          |
        1 | / false * (nil
          | ^^^^^^^ this expression is missing the left-hand operand
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        error: binary operator without right-hand operand
          --> %i0:2:7
          |  
        1 |   / false * (nil
          | /------------'
        2 | |     - ) == ()
          | |       ^ expected right-hand operand here
          | \-----' this expression is missing the right-hand operand
          |  
          = note: expected number, string, `true`, `false`, `nil` or `(`

        error: parentheses closed prematurely
          --> %i0:2:13
          |
        2 |     - ) == ()
          |            -^ parentheses closed here, prematurely
          |            | 
          |            parentheses opened here
          |
          = note: expected number, string, `true`, `false`, `nil` or `(`

        "#);
    });
}

#[test]
// TODO Parser actually can't detect this one yet, it just assumes it's at the end of an
// expression and quits lol
#[ignore = "parser not equipped to detect this condition yet"]
fn err_spurious_close_paren() {
    with_new_interpreter(|_| {
        parse_source("45 - nil ) / false");
        assert_snapshot!(render_dcx(), @"");
    });
}
