use super::Stmt;
use crate::session::Session;
use crate::util::test::parse_new_source;

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
