//! Structured Query Language (SQL).
//!
//! This module defines data structures for a limited form of SQL, and
//! implements conversion to it from the tuple relational calculus (see the
//! [`trc`] module). This conversion only succeeds if the query is range
//! restricted, which guarantees domain independence.
//!
//! [`trc`]: ../trc/index.html

use std::convert::{TryFrom, TryInto};
use std::mem;

use map::OrderMap;
use ops;
use trc;
use ulc::Term;

/// Style options for conversion to SQL.
#[derive(Debug, PartialEq, Eq)]
pub struct Style {
    /// Use joins ("INNER", "CROSS") instead of selecting from multiple tables.
    pub join: bool,
    /// Use semijoins ("WHERE EXISTS") where possible.
    pub semijoin: bool,
    /// Use "SELECT DISTINCT" and "UNION" rather than "SELECT" and "UNION ALL".
    pub distinct: bool,
    /// Pretty-print the output instead of putting it on one line.
    pub pretty: bool,
}

/// Error type for conversions to SQL.
#[derive(Debug, PartialEq, Eq)]
pub enum Error<'a> {
    /// The tuple relational calculus formula is not range restricted.
    NotRangeRestricted(&'a trc::Formula<'a>),
    /// A free variable in the result tuple does not appear in the formula.
    UnconstrainedVariable(&'a str),
    // /// An unexpected `trc::Formula::Rel` term was found.
    // UnexpectedRel(Term<'a>),
    // /// An unexpected `trc::Formula::Exists` term was found.
    // UnexpectedExists(Term<'a>),
}

/// A top-level SQL query.
#[derive(Debug, PartialEq, Eq)]
pub struct TopQuery<'a> {
    /// The expressions to select.
    cols: Vec<Expression<'a>>,
    /// The underlying query for the free variables in `cols`.
    sel: Select<'a>,
}

/// A query that selects the values of free variables.
#[derive(Debug, PartialEq, Eq)]
struct Query<'a> {
    /// One or more selections, the union of which form the query.
    sels: Vec<Select<'a>>,
}

/// A map from free variables to expressions that determine their values.
type VarMap<'a> = OrderMap<&'a str, Expression<'a>>;

/// A vector of conjuncts forming a condition.
type Condition<'a> = Vec<Formula<'a>>;

/// A selection of expressions from one or more tables.
#[derive(Debug, PartialEq, Eq)]
struct Select<'a> {
    /// The free variables to select.
    map: VarMap<'a>,
    /// One or more tables to select from, and their "ON" clauses.
    tables: Vec<(Table<'a>, Condition<'a>)>,
    /// The "WHERE" clause.
    cond: Condition<'a>,
}

/// A SQL table expression.
#[derive(Debug, PartialEq, Eq)]
enum Table<'a> {
    /// A named table in the database.
    Named(&'a str),
    /// A table produced by a subquery.
    Sub(Query<'a>),
}

/// A group of indices specifying a column in a query.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
struct Column {
    /// Index of the query: 0 is current, 1 is first parent, etc.
    query_index: usize,
    /// Index of the table in the query's `tables` vector.
    table_index: usize,
    /// Index of the column in the table's `cols` vector.
    column_index: usize,
}

/// An expression in a SQL query.
#[derive(Debug, PartialEq, Eq, Clone)]
enum Expression<'a> {
    /// A string constant.
    Const(&'a str),
    /// A column from a table.
    Column(Column),
    /// A function applied to a tuple of expressions.
    App(&'a str, Vec<Expression<'a>>),
}

/// A formula in a SQL query.
#[derive(Debug, PartialEq, Eq)]
enum Formula<'a> {
    /// A predicate applied to a tuple of expressions.
    Pred(&'a str, Vec<Expression<'a>>),
    /// One or two formulas joined by a logical operator.
    Logic(&'a str, Vec<Formula<'a>>),
    /// Existence operator, stating that a query has nonempty results.
    Exists(Box<Query<'a>>),
}

/// Creates a formula for equality.
fn equal<'a, T, U>(lhs: T, rhs: U) -> Formula<'a>
where
    T: Into<Expression<'a>>,
    U: Into<Expression<'a>>,
{
    Formula::Pred(ops::EQ, vec![lhs.into(), rhs.into()])
}

/// Creates a column expression for the current query.
fn column(table_index: usize, column_index: usize) -> Column {
    Column {
        query_index: 0,
        table_index,
        column_index,
    }
}

/// Converts a TRC expression to a SQL expression.
///
/// Uses the given map to convert variables in the expression. On success,
/// returns the converted expression. On failure, returns the name of the
/// variable that was not found in the map.
fn convert_expression<'a>(
    expr: &trc::Expression<'a>,
    map: &VarMap<'a>,
) -> Result<Expression<'a>, &'a str> {
    match expr {
        trc::Expression::Const(val) => Ok(Expression::Const(val)),
        trc::Expression::Var(name) => map.get(name).cloned().ok_or(name),
        trc::Expression::App(fun, args) => Ok(Expression::App(
            fun,
            args.iter()
                .map(|arg| convert_expression(arg, map))
                .collect::<Result<Vec<_>, &str>>()?,
        )),
    }
}

/// Combine multiple selections into a single selection.
fn combine<'a>(sels: Vec<Select<'a>>) -> Select<'a> {
    if sels.len() == 1 {
        sels.into_iter().next().unwrap()
    } else {
        let mut map = OrderMap::new();
        for (i, &var) in sels[0].map.keys().enumerate() {
            map.insert(var, Expression::Column(column(0, i)));
        }
        Select {
            map,
            tables: vec![(Table::Sub(Query { sels: sels }), vec![])],
            cond: vec![],
        }
    }
}

impl<'a> From<Query<'a>> for Select<'a> {
    fn from(query: Query) -> Select {
        combine(query.sels)
    }
}

impl<'a> Query<'a> {
    /// Returns a mutable reference to selection for this query.
    ///
    /// If the query is the union of multiple selections, combines them first.
    fn mut_select(&mut self) -> &mut Select<'a> {
        if self.sels.len() != 1 {
            let mut sels = vec![];
            mem::swap(&mut self.sels, &mut sels);
            self.sels.push(combine(sels));
        }
        &mut self.sels[0]
    }
}

impl<'a> From<&'a str> for Expression<'a> {
    fn from(val: &'a str) -> Expression<'a> {
        Expression::Const(val)
    }
}

impl<'a> From<Column> for Expression<'a> {
    fn from(col: Column) -> Expression<'a> {
        Expression::Column(col)
    }
}

impl<'a> TryFrom<&'a trc::Query<'a>> for TopQuery<'a> {
    type Error = Error<'a>;

    fn try_from(
        trc::Query { tuple, formula }: &'a trc::Query<'a>,
    ) -> Result<TopQuery, Error> {
        let query: Query = formula.try_into()?;
        let sel: Select = query.into();
        Ok(TopQuery {
            cols: tuple
                .iter()
                .map(|arg| convert_expression(arg, &sel.map))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|v| Error::UnconstrainedVariable(v))?,
            sel,
        })
    }
}

impl<'a> TryFrom<&'a trc::Formula<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(formula: &'a trc::Formula<'a>) -> Result<Query, Error> {
        match formula {
            trc::Formula::Rel(rel, args) => {
                let mut map: VarMap = OrderMap::new();
                let mut cond = vec![];
                for (i, arg) in args.iter().enumerate() {
                    match arg {
                        trc::Expression::Const(&val) => {
                            cond.push(equal(column(0, i), val));
                        }
                        trc::Expression::Var(name) => {
                            if let Some(expr) = map.get(name) {
                                cond.push(equal(expr.clone(), column(0, i)))
                            } else {
                                map.insert(
                                    name,
                                    Expression::Column(column(0, i)),
                                );
                            }
                        }
                        _ => (),
                    }
                }
                for (i, arg) in args.into_iter().enumerate() {
                    if let trc::Expression::App(..) = arg {
                        cond.push(equal(
                            column(0, i),
                            convert_expression(&arg, &map)
                                .or(Err(Error::NotRangeRestricted(formula)))?,
                        ));
                    }
                }
                let sel = Select {
                    map,
                    tables: vec![(Table::Named(rel), vec![])],
                    cond,
                };
                Ok(Query { sels: vec![sel] })
            }
            trc::Formula::And(box lhs, box rhs) => {
                let mut query: Query = lhs.try_into()?;
                let sel = query.mut_select();
                match rhs {
                    trc::Formula::Rel(..) => unimplemented!(),
                    trc::Formula::Equal(x, y) => match (x, y) {
                        (box trc::Expression::Var(name), ref expr)
                        | (ref expr, box trc::Expression::Var(name))
                            if !sel.map.contains_key(name) =>
                        {
                            let expr = convert_expression(expr, &sel.map).or(
                                Err(Error::NotRangeRestricted(rhs.into())),
                            )?;
                            sel.map.insert(name, expr);
                        }
                        _ => unimplemented!(),
                    },
                    trc::Formula::Not(..) => unimplemented!(),
                    _ => unimplemented!(),
                }
                Ok(query)
            }
            trc::Formula::Or(box lhs, box rhs) => unimplemented!(),
            trc::Formula::Exists(vars, box body) => unimplemented!(),
            trc::Formula::Equal(..) => unimplemented!(),
            // ^ var == const special case (or apps of consts)
            _ => Err(Error::NotRangeRestricted(formula.into())),
        }
    }
}

/// Returns true if `map` contains all the free vars of `expr`.
// fn has_free_vars(map: &VarMap, expr: &trc::Expression) -> bool {
//     expr.free_vars().iter().all(|v| map.contains_key(v))
// }

/*
impl<'a> TryFrom<trc::Formula<'a>> for Formula<'a> {
    type Error = Error<'a>;

    fn try_from(formula: trc::Formula) -> Result<Formula, Error> {
        match formula {
            trc::Formula::Rel(..) => Err(Error::UnexpectedRel(formula.into())),
            trc::Formula::Pred(fun, args) => Ok(Formula::Pred(fun, args)),
            trc::Formula::Equal(box lhs, box rhs) => {
                Ok(Formula::Pred(ops::EQ, vec![lhs, rhs]))
            }
            trc::Formula::Not(box arg) => {
                Ok(Formula::Logic(ops::NOT_S, vec![arg.try_into()?]))
            }
            trc::Formula::And(box lhs, box rhs) => Ok(Formula::Logic(
                ops::AND_S,
                vec![lhs.try_into()?, rhs.try_into()?],
            )),
            trc::Formula::Or(box lhs, box rhs) => Ok(Formula::Logic(
                ops::OR_S,
                vec![lhs.try_into()?, rhs.try_into()?],
            )),
            trc::Formula::Exists(..) => {
                Err(Error::UnexpectedExists(formula.into()))
            }
        }
    }
}
*/

/*
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
*/

// !!!!
// {(x,y) : R(x) & y = f(x)}
// -> we need Expr in all, not just Expr in top-level and Column everywhere else

// {(x,y,z) : R(x) & y = f(x, x) & z = f(y, y)}
// must clone expressions to expand
// alternative: more layers of queries
// but this is a rare case; better to just clone since it is rare

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
//   ***   x in, y not: select free var y as x from A
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
