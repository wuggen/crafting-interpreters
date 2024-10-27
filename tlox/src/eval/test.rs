use std::fmt::Write;

use indoc::indoc;
use insta::assert_snapshot;

use super::Interpreter;
use crate::diag::render::render_dcx;
use crate::session::{Session, SessionKey};
use crate::util::test::parse_new_source;

fn eval_new_source(key: &SessionKey, source: &str, output: &mut String) {
    if let Some(tree) = parse_new_source(key, source) {
        let mut output_bytes = Vec::new();
        Interpreter::with_vec_output(&mut output_bytes).eval(&tree);
        output.push_str(std::str::from_utf8(&output_bytes).unwrap());
    }
}

fn test_eval(key: &SessionKey, source: &str) -> String {
    let mut output = String::new();
    eval_new_source(key, source, &mut output);

    if key.get().dcx.has_errors() {
        writeln!(output, "--> Diagnostics:").unwrap();
        write!(output, "{}", render_dcx()).unwrap();
    }

    output
}

#[test]
fn eval_lits() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, "print nil;"), @"nil");
        assert_snapshot!(test_eval(&key, "print true;"), @"true");
        assert_snapshot!(test_eval(&key, "print false;"), @"false");
        assert_snapshot!(test_eval(&key, "print 42;"), @"42");
        assert_snapshot!(test_eval(&key, r#"print "hello lol";"#), @"hello lol");
    })
}

#[test]
fn eval_unary() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, "print -42;"), @"-42");
        assert_snapshot!(test_eval(&key, "print !true;"), @"false");
    })
}

#[test]
fn eval_binary() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, "print 3 + 4;"), @"7");
        assert_snapshot!(test_eval(&key, "print 5 == nil;"), @"false");
        assert_snapshot!(test_eval(&key, "print 5 == 5 == true;"), @"true");
        assert_snapshot!(test_eval(&key, "print 3 + 6 / 2;"), @"6");
        assert_snapshot!(test_eval(&key, "print (3 + 6) / 2;"), @"4.5");
        assert_snapshot!(test_eval(&key, "print 6 % 3 == 0;"), @"true");
        assert_snapshot!(
            test_eval(
                &key,
                r#"print "hey" + " there" + " good lookin";"#,
            ),
            @"hey there good lookin",
        );
        assert_snapshot!(test_eval(&key, r#"print "hey" != "there";"#), @"true");
        assert_snapshot!(test_eval(&key, r#"print 18.5 != "lol";"#), @"true");
        assert_snapshot!(test_eval(&key, "print 4 > 3;"), @"true");
    })
}

#[test]
fn eval_truthiness() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, "print !!42;"), @"true");
        assert_snapshot!(test_eval(&key, "print !!nil;"), @"false");
        assert_snapshot!(test_eval(&key, "print !!false;"), @"false");
        assert_snapshot!(test_eval(&key, r#"print !!"lmao";"#), @"true");
    })
}

#[test]
fn err_eval_non_num() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, "print -nil;"), @r#"
        --> Diagnostics:
        error: cannot coerce Nil to Num
          --> %i0:1:8
          |
        1 | print -nil;
          |       -^^^ expression found to be of type Nil
          |       | 
          |       value coerced due to use as an operand for this operator
          |
          = note: operator `-` expects operand of type Num

        "#);

        assert_snapshot!(test_eval(&key, "print !(5 + 10) > nil;"), @r#"
        --> Diagnostics:
        error: cannot coerce Bool to Num
          --> %i0:1:7
          |
        1 | print !(5 + 10) > nil;
          |       ^^^^^^^^^ - value coerced due to use as an operand to this operator
          |       |          
          |       expression found to be of type Bool
          |
          = note: operator `>` expects operands of type Num

        error: cannot coerce Nil to Num
          --> %i0:1:19
          |
        1 | print !(5 + 10) > nil;
          |                 - ^^^ expression found to be of type Nil
          |                 |  
          |                 value coerced due to use as an operand to this operator
          |
          = note: operator `>` expects operands of type Num

        "#);
    })
}

#[test]
fn computed_str_eq() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(&key, r#"print "hey there" == "hey " + "there";"#), @"true");
    });
}

#[test]
fn global_vars() {
    Session::with_default(|key| {
        assert_snapshot!(
            test_eval(
                &key,
                indoc! {r#"
                var a = 4;
                print a;
                print a - 6;
                "#},
            ),
            @r#"
        4
        -2
        "#,
        );

        assert_snapshot!(
            test_eval(
                &key,
                indoc! {r#"
                var a;
                print a;
                var b = 76;
                var a = -2;
                print b + a;
                "#},
            ),
            @r#"
        nil
        74
        "#,
        );
    })
}

#[test]
fn err_undeclared_vars() {
    Session::with_default(|key| {
        assert_snapshot!(
            test_eval(&key, "print 4 + nope;"),
            @r#"
        --> Diagnostics:
        error: reference to unbound variable `nope`
          --> %i0:1:11
          |
        1 | print 4 + nope;
          |           ^^^^ variable is not bound at this point

        "#,
        );

        assert_snapshot!(
            test_eval(&key, "var a = 8; print a + b;"),
            @r#"
        --> Diagnostics:
        error: reference to unbound variable `b`
          --> %i0:1:22
          |
        1 | var a = 8; print a + b;
          |                      ^ variable is not bound at this point

        "#,
        );
    })
}

#[test]
fn assignment() {
    Session::with_default(|key| {
        assert_snapshot!(
            test_eval(
                &key,
                indoc !{r#"
                var a = 4;
                print a;
                a = 6;
                print a;
                print a = a + 4;
                print a;
                "#},
            ),
            @r#"
        4
        6
        10
        10
        "#,
        );

        assert_snapshot!(
            test_eval(
                &key,
                indoc !{r#"
                var a; var b; var c;
                a = b = c = 1;
                print a; print b; print c;
                "#},
            ),
            @r#"
        1
        1
        1
        "#,
        );
    })
}

#[test]
fn err_assignment_unbound_var() {
    Session::with_default(|key| {
        assert_snapshot!(
            test_eval(&key, "a = 45;"),
            @r#"
        --> Diagnostics:
        error: assignment to unbound variable `a`
          --> %i0:1:1
          |
        1 | a = 45;
          | ^ variable is not bound at this point

        "#,
        );

        assert_snapshot!(
            test_eval(&key, "var x; print x = a = x;"),
            @r#"
        --> Diagnostics:
        error: assignment to unbound variable `a`
          --> %i0:1:18
          |
        1 | var x; print x = a = x;
          |                  ^ variable is not bound at this point

        "#,
        );
    })
}
