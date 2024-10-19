use std::fmt::Debug;

use insta::assert_snapshot;

use super::Interpreter;
use crate::diag::render::render_dcx;
use crate::session::{Session, SessionKey};
use crate::util::test::parse_new_source;
use crate::val::Value;

const NONE_VAL: Option<Value> = None;

fn eval_new_source<'s>(key: SessionKey<'s>, source: &str) -> Option<Value<'s>> {
    let tree = parse_new_source(key, source)?;
    Interpreter.eval(&tree)
}

fn test_eval<T>(key: SessionKey, source: &str, expected: Option<T>, render_diags: bool)
where
    for<'s> Value<'s>: PartialEq<T>,
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

    let val = eval_new_source(key, source);

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
    Session::with_default(|key| {
        test_eval(key, "nil", Some(Value::Nil), true);
        test_eval(key, "true", Some(true), true);
        test_eval(key, "false", Some(false), true);
        test_eval(key, "42", Some(42.0), true);
        test_eval(key, r#""hello lol""#, Some("hello lol"), true);
    })
}

#[test]
fn eval_unary() {
    Session::with_default(|key| {
        test_eval(key, "-42", Some(-42.0), true);
        test_eval(key, "!true", Some(false), true);
    })
}

#[test]
fn eval_binary() {
    Session::with_default(|key| {
        test_eval(key, "3 + 4", Some(7.0), true);
        test_eval(key, "5 == nil", Some(false), true);
        test_eval(key, "5 == 5 == true", Some(true), true);
        test_eval(key, "3 + 6 / 2", Some(6.0), true);
        test_eval(key, "(3 + 6) / 2", Some(4.5), true);
        test_eval(key, "6 % 3 == 0", Some(true), true);
        test_eval(
            key,
            r#""hey" + " there" + " good lookin""#,
            Some("hey there good lookin"),
            true,
        );
        test_eval(key, r#""hey" != "there""#, Some(true), true);
        test_eval(key, r#"18.5 != "lol""#, Some(true), true);
        test_eval(key, "4 > 3", Some(true), true);
    })
}

#[test]
fn eval_truthiness() {
    Session::with_default(|key| {
        test_eval(key, "!!42", Some(true), false);
        test_eval(key, "!!nil", Some(false), false);
        test_eval(key, "!!false", Some(false), false);
        test_eval(key, r#"!!"lmao""#, Some(true), false);
    })
}

#[test]
fn err_eval_non_num() {
    Session::with_default(|key| {
        test_eval(key, "-nil", NONE_VAL, false);
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

        test_eval(key, "!(5 + 10) > nil", NONE_VAL, false);
        assert_snapshot!(render_dcx(), @r#"
        error: cannot coerce Bool to Num
          --> %i0:1:1
          |
        1 | !(5 + 10) > nil
          | ^^^^^^^^^ - value coerced due to use as an operand to this operator
          | |          
          | expression found to be of type Bool
          |
          = note: operator `>` expects operands of type Num

        error: cannot coerce Nil to Num
          --> %i0:1:13
          |
        1 | !(5 + 10) > nil
          |           - ^^^ expression found to be of type Nil
          |           |  
          |           value coerced due to use as an operand to this operator
          |
          = note: operator `>` expects operands of type Num

        "#);
    })
}

#[test]
fn computed_str_eq() {
    Session::with_default(|key| {
        test_eval(key, r#""hey there" == "hey " + "there""#, Some(true), true);
    });
}
