use std::fmt::Debug;

use insta::assert_snapshot;

use crate::context::with_new_session;
use crate::diag::render::render_dcx;
use crate::util::test::parse_new_source;
use crate::val::Value;

use super::Interpreter;

const NONE_VAL: Option<Value> = None;

fn eval_new_source(source: &str) -> Option<Value> {
    let tree = parse_new_source(source)?;
    let interp = Interpreter {};
    interp.eval(&tree)
}

fn test_eval<T>(source: &str, expected: Option<T>, render_diags: bool)
where
    Value: PartialEq<T>,
    T: Debug,
{
    let report = |val, expected| {
        eprintln!("!! Unexpected evaluation");
        eprintln!("--> Input:");
        for line in source.lines() {
            eprintln!(" | {line}");
        }
        eprintln!("--> Expected: {expected:?}");
        eprintln!("--> Evaluated: {val:?}");
        if render_diags {
            eprintln!("--> Diagnostics:");
            eprintln!("{}", render_dcx());
        }
        panic!();
    };

    let val = eval_new_source(source);

    match (&val, &expected) {
        (Some(v), Some(e)) if v != e => {
            report(val, expected);
        }

        (Some(_), None) | (None, Some(_)) => {
            report(val, expected);
        }

        _ => {}
    }
}

#[test]
fn eval_lits() {
    with_new_session(|_| {
        test_eval("nil", Some(Value::Nil), true);
        test_eval("true", Some(true), true);
        test_eval("false", Some(false), true);
        test_eval("42", Some(42.0), true);
        test_eval(r#""hello lol""#, Some("hello lol"), true);
    })
}

#[test]
fn eval_unary() {
    with_new_session(|_| {
        test_eval("-42", Some(-42.0), true);
        test_eval("!true", Some(false), true);
    })
}

#[test]
fn eval_binary() {
    with_new_session(|_| {
        test_eval("3 + 4", Some(7.0), true);
        test_eval("5 == nil", Some(false), true);
        test_eval("5 == 5 == true", Some(true), true);
        test_eval("3 + 6 / 2", Some(6.0), true);
        test_eval("(3 + 6) / 2", Some(4.5), true);
        test_eval("6 % 3 == 0", Some(true), true);
        test_eval(
            r#""hey" + " there" + " good lookin""#,
            Some("hey there good lookin"),
            true,
        );
        test_eval(r#""hey" != "there""#, Some(true), true);
        test_eval(r#"18.5 != "lol""#, Some(true), true);
        test_eval("4 > 3", Some(true), true);
    })
}

#[test]
fn eval_truthiness() {
    with_new_session(|_| {
        test_eval("!!42", Some(true), false);
        test_eval("!!nil", Some(false), false);
        test_eval("!!false", Some(false), false);
        test_eval(r#"!!"lmao""#, Some(true), false);
    })
}

#[test]
fn err_eval_non_num() {
    with_new_session(|_| {
        test_eval("-nil", NONE_VAL, false);
        assert_snapshot!(render_dcx(), @r#"
        error: cannot coerce Nil to Num
          --> %i0:1:2
          |
        1 | -nil
          | -^^^ expression found to be of type Nil
          | | 
          | value coerced due to use as an operand for this operator
          |
          = note: operator `-` expects operand of type Num

        "#);
    })
}
