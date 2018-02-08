//! Tuple relational calculus parser.

use query::*;

use nom::{alphanumeric, digit};

use std::str::from_utf8 as utf8;

named!(query<&[u8], Query>,
    do_parse!(
        char!('{') >>
        tuple: tuple >>
        char!(':') >>
        formula: formula >>
        char!('}') >>
        (Query { tuple, formula })
    )
);

named!(tuple<&[u8], Tuple>,
    delimited!(
        char!('('),
        separated_list_complete!(char!(','), expression),
        char!(')')
    )
);

named!(expression<&[u8], Expression>,
    alt!(
        delimited!(
            char!('('), expression, char!(')')
        ) | do_parse!(
            val: map_res!(digit, utf8) >>
            (Expression::Const { val, typ: Type::Number })
        ) | do_parse!(
            val: map_res!(
                delimited!(char!('\''), is_not!("'"), char!('\'')), utf8) >>
            (Expression::Const { val, typ: Type::Text })
        ) | do_parse!(
            name: map_res!(alphanumeric, utf8) >>
            (Expression::Var { name })
        ) | do_parse!(
            lhs: expression >>
            op: map_res!(
                alt!(tag!("*") | tag!("/") | tag!("+") | tag!("-")), utf8) >>
            rhs: expression >>
            (Expression::App { op, args: vec![lhs, rhs]})
        )
    )
);

named!(formula<&[u8], Formula>,
    alt!(
        delimited!(
            char!('('), formula, char!(')')
        ) | do_parse!(
            char!('!') >>
            f: formula >>
            (Formula::Conn { op: Connective::Not, args: vec![f] })
        ) | do_parse!(
            lhs: formula >>
            op: one_of!("&|") >>
            rhs: formula >>
            (Formula::Conn {
                op: if op == '&' { Connective::And } else { Connective::Or },
                args: vec![lhs, rhs]
            })
        ) | do_parse!(
            lhs: expression >>
            op: map_res!(alt!(tag!("=") | tag!("<") | tag!(">") | tag!("<=")
                | tag!(">=") | tag_no_case!("LIKE")), utf8) >>
            rhs: expression >>
            (Formula::App { op, args: vec![lhs, rhs] })
        ) | do_parse!(
            op: map_res!(alphanumeric, utf8) >>
            args: tuple >>
            (Formula::Rel { op, args })
        )
    )
);

#[cfg(test)]
mod tests {
    use super::*;
    use nom::IResult;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn test_foo() {
        let f = b"{(x):R(x)&Q(x)}";
        println!("{:?}", query(f))
        /*assert_eq!(
            query(f),
            IResult::Done(
                &[][..],
                Query {
                    tuple: vec![],
                    formula: Formula::Conn {
                        op: Connective::And,
                        args: vec![],
                    },
                }
            )
        );*/
    }
}
