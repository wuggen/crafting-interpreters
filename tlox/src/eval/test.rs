use insta::assert_snapshot;

use super::Interpreter;
use crate::diag::render::render_dcx;
use crate::session::{Session, SessionKey};
use crate::util::test::parse_new_source;

fn eval_new_source(key: SessionKey, source: &str) -> Option<String> {
    let tree = parse_new_source(key, source)?;
    let mut output = Vec::new();
    Interpreter::with_vec_output(&mut output).eval(&tree);
    Some(String::from_utf8(output).unwrap())
}

fn test_eval(key: SessionKey, source: &str, render_diags: bool) -> Option<String> {
    let output = eval_new_source(key, source);
    if render_diags {
        eprintln!("--> Diagnostics:");
        eprintln!("{}", render_dcx());
    }
    output
}

#[test]
fn eval_lits() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(key, "print nil;", true).unwrap(), @"nil");
        assert_snapshot!(test_eval(key, "print true;", true).unwrap(), @"true");
        assert_snapshot!(test_eval(key, "print false;", true).unwrap(), @"false");
        assert_snapshot!(test_eval(key, "print 42;", true).unwrap(), @"42");
        assert_snapshot!(test_eval(key, r#"print "hello lol";"#, true).unwrap(), @"hello lol");
    })
}

#[test]
fn eval_unary() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(key, "print -42;", true).unwrap(), @"-42");
        assert_snapshot!(test_eval(key, "print !true;", true).unwrap(), @"false");
    })
}

#[test]
fn eval_binary() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(key, "print 3 + 4;", true).unwrap(), @"7");
        assert_snapshot!(test_eval(key, "print 5 == nil;", true).unwrap(), @"false");
        assert_snapshot!(test_eval(key, "print 5 == 5 == true;", true).unwrap(), @"true");
        assert_snapshot!(test_eval(key, "print 3 + 6 / 2;", true).unwrap(), @"6");
        assert_snapshot!(test_eval(key, "print (3 + 6) / 2;", true).unwrap(), @"4.5");
        assert_snapshot!(test_eval(key, "print 6 % 3 == 0;", true).unwrap(), @"true");
        assert_snapshot!(
            test_eval(
                key,
                r#"print "hey" + " there" + " good lookin";"#,
                true,
            ).unwrap(),
            @"hey there good lookin",
        );
        assert_snapshot!(test_eval(key, r#"print "hey" != "there";"#, true).unwrap(), @"true");
        assert_snapshot!(test_eval(key, r#"print 18.5 != "lol";"#, true).unwrap(), @"true");
        assert_snapshot!(test_eval(key, "print 4 > 3;", true).unwrap(), @"true");
    })
}

#[test]
fn eval_truthiness() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(key, "print !!42;", false).unwrap(), @"true");
        assert_snapshot!(test_eval(key, "print !!nil;", false).unwrap(), @"false");
        assert_snapshot!(test_eval(key, "print !!false;", false).unwrap(), @"false");
        assert_snapshot!(test_eval(key, r#"print !!"lmao";"#, false).unwrap(), @"true");
    })
}

#[test]
fn err_eval_non_num() {
    Session::with_default(|key| {
        assert_snapshot!(test_eval(key, "print -nil;", false).unwrap(), @"");
        assert_snapshot!(render_dcx(), @r#"
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

        assert_snapshot!(test_eval(key, "print !(5 + 10) > nil;", false).unwrap(), @"");
        assert_snapshot!(render_dcx(), @r#"
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
        assert_snapshot!(test_eval(key, r#"print "hey there" == "hey " + "there";"#, true).unwrap(), @"true");
    });
}
