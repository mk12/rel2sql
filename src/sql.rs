//! Structured Query Language (SQL).
//!
//! This module defines data structures for a limited form of SQL, and
//! implements conversion to it from the tuple relational calculus (see the
//! [`trc`] module). This conversion only succeeds if the query is range
//! restricted, which guarantees domain independence.
//!
//! [`trc`]: ../trc/index.html

use std::convert::{TryFrom, TryInto};
use std::fmt;

use ops::Logic;
use trc;

/// A SQL query that selects values of free variables.
pub struct Query<'a> {
    /// The columns to select.
    pub cols: Vec<(&'a str, Column)>,
    /// The tables to select from.
    pub tables: Vec<Table<'a>>,
    /// The "WHERE" clause, as a vector of conjuncts.
    pub cond: Vec<Formula<'a>>,
}

/// A SQL table expression.
pub enum Table<'a> {
    /// A named table in the database.
    Named(&'a str),
    /// A table produced by a subquery.
    Query(Query<'a>),
}

// A group of indices specifying a column in a query.
pub struct Column {
    /// Index of the query: 0 is current, 1 is first parent, etc.
    pub query_index: usize,
    /// Index of the table in the query's `tables` vector.
    pub table_index: usize,
    /// Index of the column in the table's `cols` vector.
    pub column_index: usize,
}

/// An expression in a SQL query.
pub enum Expression<'a> {
    /// A string constant.
    Const(&'a str),
    /// A column from a table.
    Column(Column),
    /// A function applied to a tuple of expressions.
    App(&'a str, Vec<Expression<'a>>),
}

/// A formula in a SQL query.
pub enum Formula<'a> {
    /// A predicate applied to a tuple of expressions.
    Pred(&'a str, Vec<Expression<'a>>),
    /// One or two formulas joined by a logical operator.
    Logic(Logic, Vec<Formula<'a>>),
    /// Existence operator, stating that a query has nonempty results.
    Exists(Box<Query<'a>>),
}

/// Error type for conversions to SQL.
pub enum Error<'a> {
    NotRangeRestricted(&'a str),
}

impl<'a> Query<'a> {
    // TODO
}

impl<'a> TryFrom<trc::Formula<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(formula: trc::Formula) -> Result<Query, Error> {
        match formula {
            trc::Formula::Rel(rel, args) => {
                let mut query = Query {
                    cols: vec![],
                    tables: vec![Table::Named(rel)],
                    cond: vec![],
                };
                for (i, arg) in args.iter().enumerate() {
                    match arg {
                        trc::Expression::Const(val) => {
                            query.cond.push(Formula::Pred(
                                "=",
                                vec![
                                    Expression::Column(Column {
                                        query_index: 0,
                                        table_index: 0,
                                        column_index: i,
                                    }),
                                    Expression::Const(val),
                                ],
                            ))
                        }
                        trc::Expression::Var(name) => {
                            // if name already in cols free vars:
                            // then: add conjunct making them equal
                            // else: add col for this free var
                            unimplemented!()
                        }
                        trc::Expression::App(fun, args) => {}
                    }
                }
                unimplemented!()
            }
            trc::Formula::Logic(Logic::And, vec![lhs, rhs]) => unimplemented!(),
            trc::Formula::Pred(fun, args) => unimplemented!(),
            trc::Formula::Logic(op, args) => unimplemented!(),
            trc::Formula::Exists(vars, body) => unimplemented!(),
        }
    }
}

// R(...)
// A & B
// A & x=y (intersection)
// A | B  (eq)
// A & !B (subset)
// A & p(...) (subset)

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(2, 2);
    }
}

// TODO:
// - helper for Equality expr
// - maybe don't include free var name in Column

// advantage of Query->Query, Formula->Subquery
// but want to mutate at end to avoid wrapper query

// KEY POINT:
// not pure divide and conquer.
// instead, divide, conquer LHS, and then mutate that result based on RHS of &.
// (or vice versa)
// (l,r) or (r,l) is more powerful than I thought -> if one fails, it tries the
// other, so (((a&b)&c)&d)&e parses as:
//       *            just by swapping L/R branches of this tree one at a time,
//      / \            you are effectively swapping positions in a linked list
//     / \ e          (since it is a degenreate, anti fox news tree), which means
//    / \ d          you can achieve all of the 5! orders (I think) ... or maybe
//   /\ c            not .. well you swap or not 5 times so 2^5 = 32 possible
//  a b              orders? Let's try a smaller example
//
//        *         3! = 6 would be abc acb bac bca cab cba
//       / \        2^2 = 4 would be...
//      *  c           abc bac cab cba --- missing acb bca
//     / \
//    a  b

// {(x) : foo(x) & bar(x)}

// SELECT f.a AS x FROM foo as f, bar as b WHERE b.a = f.a;

// SELECT x FROM (SELECT a AS x FROM bar) AS t1, (SELE)]

// table+col index: needs to know order of variables
// free var name: won't clash

// {(x, y+1) | (Foo(x) /\ Bar(y)) \/ (Foo(y) /\ Bar(x))}

// SELECT t0.x, t0.y + 1
// FROM
//  (SELECT t1.x, t1.y
//    FROM (SELECT t2.x AS x, t3.y AS y FROM Foo AS t2, Bar AS t3) AS t1
//  UNION
//    SELECT t.x, t.y
//    FROM () AS t
//  ) AS t0;

/*
impl<'a> TryFrom<trc::Query<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(query: trc::Query) -> Result<Query, Error> {
        Ok(Query {
            tuple:
        })
    }
}
*/

/*
impl<'a> TryFrom<trc::Formula<'a>> for Subquery<'a> {
    type Error = Error<'a>;

    fn try_from(formula: trc::Formula) -> Result<Subquery, Error> {
        match formula {
            trc::Formula::Rel(rel, args) => {
                let conds = vec![];
                for (i, a) in args.iter().enumerate() {
                    match a {
                        trc::Expression::Const(val) => conds.push(Pred("=", vec![Column(0, i), val])),
                        trc::Expression::Var(name) =>
                        trc::Expression::App(fun, args) => conds.push(Pred("=", vec![Column(0, i), val]))

                        // {(x) : R(x) & S(x+1)}
                        // -> rewrite {(x) : exists y . R(x) & S(y) & x=y+1}

                        // select _0 from
                        //   (select t0._0, t0._1 from
                        //     (select t0._0, t1._0
                        //      from (select _0 from R) as t0, (select _0 from S) as t1)
                        //      where t0._0 = t0._1 + 1)
                        //    )

                        // rather than have (exists x . ...) wrap a subquery, should be possible to just 
                        // mutate the list of the inner (or produce a new thing as a function of the old
                        // one to avoid mutation)
                        // similary, converting (...) & x=y+1 should just append to its conditions
                        // i.e. for a given range-restricted formula, rahterh than recursively evaluating children
                        // and produing a superstrucure on top, can just convert LHS and then modify it based on the
                        // unconverted LHS

// note: UNION (not UNION ALL), SELECT DISTINCT (not SELECT)
// config?
                        // R(x, ...) -> standalone subquery
                        // a & b -> general case two subqueries, but a & R(...) special case can add to tables of converted a?
                        // a & x=y   -> both in FV: add to cond;  one in FV: add to vars/tuple
                        // a | b (FV =) -> union; special case for R(...) | R(...)
                        // a & !b (FV subset) -> add cond: NOT EXISTS ( ... ) ? // prob: refercing outer vars inside that.. need to link up
                        // a & P(...) (FB subset) -> add to cond of a
                        // exists x . a -> remove x from vars/tuple
                        
                        // note: if And is a list of all conjuncts, could try all possible pairs to find
                        // one that works.... right now though I would just do both sides, i.e.
                        // phi & x=y
                        // x=y & phi
                        // but (((a&b)&c)&d)&e will not work if actually RR by a&(b&(c&(d&e)))
                        // --> YES IT WILL (see above about 2^n not n! permutations)
                    }
                } // R(x, y) & !S(x)
            }
            trc::Formula::Pred(pred, args) => {
                Err(Error::Foo("a"))
            }
            trc::Formula::Logic(op, args) => {
                Err(Error::Foo("a"))
            }
            trc::Formula::Exists(vars, body) => {
                Err(Error::Foo("a"))
            }
        }
    }
}

// UNDECIDABLE!
// stick strictly to range-restricted, then it can be done recursively, each step
// generating a subquery that gets all its free variables.
// can try (lhs,rhs) and (rhs,lhs) but otherwise assume user enters RR relcalc.
// challenge: Simplify this SQL with all these SELECT .. FROM (SELECT FROM .. ) as t
// where subquery is unnecessary.

// params:
// prettyindenent / one line
// schema / numbered
// impl<'a> fmt::Display for Query<'a> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "SELECT DISTINCT {}")
//     }
// }

*/
