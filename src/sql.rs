//! Structured Query Language (SQL).
//!
//! This module defines data structures for a limited form of SQL, and
//! implements conversion to it from the tuple relational calculus (see the
//! [`trc`] module). This conversion only succeeds if the query is range
//! restricted, which guarantees domain independence.
//!
//! [`trc`]: ../trc/index.html

use std::collections::{HashMap, HashSet};
use std::convert::{TryFrom, TryInto};
use std::fmt;

use trc;
use ulc;

/// A top-level SQL query.
pub struct Query<'a> {
    /// The expressions to select.
    exprs: Vec<Expression<'a>>,
    /// Query to get free variables from.
    union: Union<'a>
}

/// A query that selects the values of free variables.
struct Union<'a> {
    /// The free variables to select.
    vars: HashSet<&'a str>,
    /// The queries to combine with "UNION".
    sels: Vec<Select<'a>>,
}

/// A query that joins one or more tables.
struct Select<'a> {
    /// The tables to select from.
    tables: Vec<Table<'a>>,
    /// The "WHERE" clause, as a vector of conjuncts.
    cond: Vec<Formula<'a>>,
}

/// A SQL table expression.
enum Table<'a> {
    /// A named table in the database.
    Named(&'a str, HashMap<&'a str, usize>),
    /// A table produced by a subquery.
    Sub(Union<'a>),
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
    Logic(&'a str, Vec<Formula<'a>>),
    /// Existence operator, stating that a query has nonempty results.
    Exists(Box<Query<'a>>),
}

/// Style options for conversion to SQL.
pub struct Style {
    /// Use joins (INNER and CROSS) instead of selecting from multiple tables.
    pub join: bool,
    /// Use semijoins (WHERE EXISTS) where possible.
    pub semijoin: bool,
    /// Use SELECT DISTINCT and UNION instead of SELECT and UNION ALL.
    pub distinct: bool,
    /// Pretty-print the output instead of putting it on one line.
    pub pretty: bool,
}

/// Error type for conversions to SQL.
pub enum Error<'a> {
    /// The tuple relational calculus formula is not range restricted.
    NotRangeRestricted(ulc::Term<'a>),
}

impl<'a> TryFrom<trc::Query<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(query: trc::Query) -> Result<Query, Error> {
        Err(Error::NotRangeRestricted(ulc::Term::Const("X")))
    }
}

impl<'a> TryFrom<trc::Formula<'a>> for Union<'a> {
    type Error = Error<'a>;

    fn try_from(formula: trc::Formula) -> Result<Union, Error> {
        match formula {
            trc::Formula::Rel(rel, args) => {
                let mut vars = vec![];
                let mut map = HashMap::new();
                let mut un = Join {
                    tables: vec![Table::Named(rel),
                    cond: vec![],
                };
                for (i, arg) in args.iter().enumerate() {
                    match arg {
                        trc::Expression::Const(val) => {
                            sel.cond.push(Formula::Pred(
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
                        _ => (),
                    }
                }
                for (i, arg) in args.into_iter().enumerate() {
                    match arg {
                        trc::Expression::App(..) => {
                            return Err(Error::NotRangeRestricted(arg.into()));
                        }
                    }
                }
                Union {
                    vars,
                    joins: vec![Join]
                }
            }
            trc::Formula::Pred(fun, args) => unimplemented!(),
            trc::Formula::Equal(lhs, rhs) => unimplemented!(),
            trc::Formula::Not(arg) => unimplemented!(),
            trc::Formula::And(lhs, rhs) => unimplemented!(),
            trc::Formula::Or(lhs, rhs) => unimplemented!(),
            trc::Formula::Exists(vars, body) => unimplemented!(),
        }
    }
}

// R(...)
//     const -> append = conjunct
//     var ->
//         new: add select free var
//         recur: append = conjunct
//     app -> fail
// A & R(...)
//     recur on A, then
//         (special case if R in A's tables) -> just don't add! UNLESS SELF-JOIN.
//         1. add R to A's tables
//         2. go through each
//             const -> append = conjunct
//             var ->
//                 new: add select free var
//                 recur (from any): append = conjunct
//             app ->
//                 all recur: append = conjunct
// A & x=y (intersection)
//     recur on A, then
//         x in, y not: select free var y as x from A
//         y in, x not: symmetrical
//         x in, y in: append = conjunct to A
//         neither in: fail
//         ("x not" <=> "f(x)")
// A & !B (subset)
//     recur on A, recur on B, then append conjunct:
//         NOT EXISTS (<B> append = conjuncts)
//         (and check subset explicitly)
// A & p(...) (subset)
//     append conjunct
// A & B
//     FIRST, check if one's free vars is a subset of the other.
//     recur on A, recur on B, then
//         SELECT a1, a2, b1, b2, ... FROM (SELECT ...) AS _, (SELECT ...) AS _
//         for each intersection, append = conjunct
//     if B not RR, see if it is just a complicated predicate (no rels, no new vars)
// A | B  (eq)
//     recur on A and B, get vars in same order, union
//     (check they have same vars!)
// exists x. A
//     recur on A, remove x from cols

// NOTE:  Might need to delay table -> where exists transformation.
// e.g. R(x,z) & Q(x,y) -> ok need multiple tables / join
//  -> exists y. R(x,z) & Q(x,y) -> now it can be transformed

// semijoin optimizaiont problem: remove table from list means shifting all indices

// R(x,5) | R(x,6)
// exists y . R(x,y) & (y=5|y=6)

// idea: select from t1, t2, t3 could be changed to joins, but woudl need to
// remember which conjuncts are the ON conditions
// could also optimize semi-join if table is not referenced in cols

// Q: Should it be:
// 1. Query { tables: Vec<Table::Named | Table::Query{ query }>}, ... or
// 2. Query::Query { tables: Vec<Query>} | Query::Base/Named
// (1) because (2) doesn't make sense in the context of SELECT .. FROM t1, t2
// -- multiple base tables selected from.

// idea: treat R(...) & (| & | && )
//                      ^^^^^^^^^^^
//  as one big predicate if all subset (no new vars)

// note: no typechking. but R(x) | R(x,y) is incorrect!

//(R(x) & S(x)) & ((R(f(x)) & S(f(x))))

/// R(x,y) & (p(1) | q(2) & ((z(3) & w(2)) | q(4))

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
