//! Tuple relational calculus.
//!
//! This module defines tuple relational calculus (TRC) data structures and
//! implements conversions to and from the untyped lambda calculus (see the
//! [`ulc`] module). The conversion from ULC can fail, since TRC distinguishes
//! formulas from terms (though there is no typechecking beyond this), and
//! recognizes predefined operators from the [`ops`] module. Conversion back to
//! ULC always succeeds.
//!
//! [`ulc`]: ../ulc/index.html
//! [`ops`]: ../ops/index.html

use std::collections::HashSet;
use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::error;

use ops::{self, Kind};
use ulc::{self, Term};
use util::{into_vec, try_into_box, try_into_vec, try_into_box_2};

/// A query in the tuple relational calculus.
///
/// A query consists of a tuple and a formula. The answer to the query is the
/// value of the tuple under all valuations of free variables satisfying the
/// formula with respect to some database instance.
///
/// The lifetime 'a is the lifetime of all strings referenced in the query. This
/// makes it possible to avoid making any copies
#[derive(Debug, PartialEq, Eq)]
pub struct Query<'a> {
    /// The result tuple, usually containing Var expressions.
    pub tuple: Tuple<'a>,
    /// The query formula.
    pub formula: Formula<'a>,
}

/// A tuple of expressions.
pub type Tuple<'a> = Vec<Expression<'a>>;

/// An expression in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    /// A string constant.
    Const(&'a str),
    /// A named variable.
    Var(&'a str),
    /// A function applied to a tuple of expressions.
    App(&'a str, Tuple<'a>),
}

/// A formula in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula<'a> {
    /// A relation applied to a tuple of expressions.
    Rel(&'a str, Tuple<'a>),
    /// A predicate applied to a tuple of expressions.
    Pred(&'a str, Tuple<'a>),
    /// Equality of two expressions (special case of Pred).
    Equal(Box<Expression<'a>>, Box<Expression<'a>>),
    /// Negation of a formula.
    Not(Box<Formula<'a>>),
    /// Conjunction of two formulas.
    And(Box<Formula<'a>>, Box<Formula<'a>>),
    /// Disjunction of two formulas.
    Or(Box<Formula<'a>>, Box<Formula<'a>>),
    /// A formula exisentially quantified by a list of bound variables.
    Exists(Vec<&'a str>, Box<Formula<'a>>),
}

/// Error type for conversions to the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Error<'a> {
    /// Failure of a term to convert to an expression.
    NotExpression(&'a Term<'a>),
    /// Failure of a term to convert to a formula.
    NotFormula(&'a Term<'a>),
    /// An unexpected internal error.
    Internal(&'static str),
}

impl<'a> Expression<'a> {
    /// Returns the free variables of the expression.
    pub fn free_vars(&self) -> HashSet<&str> {
        let mut set = HashSet::new();
        self.free_vars_helper(&mut set);
        set
    }

    /// Helper function for `free_vars`.
    fn free_vars_helper(&self, set: &mut HashSet<&'a str>) {
        match self {
            Expression::Var(name) => {
                set.insert(name);
            }
            Expression::App(_, args) => for arg in args {
                arg.free_vars_helper(set)
            },
            _ => (),
        }
    }
}

impl<'a> Formula<'a> {
    /// Returns the free variables of the formula.
    pub fn free_vars(&self) -> HashSet<&str> {
        let mut set = HashSet::new();
        self.free_vars_helper(&mut set);
        set
    }

    /// Helper function for `free_vars`.
    fn free_vars_helper(&self, set: &mut HashSet<&'a str>) {
        match self {
            Formula::Rel(_, args) | Formula::Pred(_, args) => for arg in args {
                arg.free_vars_helper(set);
            },
            Formula::Equal(box lhs, box rhs) => {
                lhs.free_vars_helper(set);
                rhs.free_vars_helper(set);
            }
            Formula::Not(box arg) => {
                arg.free_vars_helper(set);
            }
            Formula::And(box lhs, box rhs) | Formula::Or(box lhs, box rhs) => {
                lhs.free_vars_helper(set);
                rhs.free_vars_helper(set);
            }
            Formula::Exists(vars, box body) => {
                body.free_vars_helper(set);
                for var in vars {
                    set.remove(var);
                }
            }
        }
    }

    /// Returns true if the formula is a Rel, or has Rel anywhere within it.
    pub fn has_rel(&self) -> bool {
        match self {
            Formula::Rel(..) => true,
            Formula::Not(box f) | Formula::Exists(_, box f) => f.has_rel(),
            Formula::And(box f1, box f2) | Formula::Or(box f1, box f2) => {
                f1.has_rel() || f2.has_rel()
            }
            _ => false,
        }
    }
}

impl<'a> From<&'static str> for Error<'a> {
    fn from(s: &'static str) -> Error {
        Error::Internal(s)
    }
}

impl<'a> error::Error for Error<'a> {
    fn description(&self) -> &str {
        match self {
            Error::NotExpression(..) => "Not an expression",
            Error::NotFormula(..) => "Not a formula",
            Error::Internal(info) => info,
        }
    }
}

impl<'a> fmt::Display for Error<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::NotExpression(term) => {
                write!(f, "Expected an expression: {}", term)
            }
            Error::NotFormula(term) => {
                write!(f, "Expected a formula: {}", term)
            }
            Error::Internal(info) => {
                write!(f, "An internal error occurred: {}", info)
            }
        }
    }
}

impl<'a> TryFrom<&'a ulc::Query<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(
        ulc::Query { tuple, formula }: &'a ulc::Query<'a>,
    ) -> Result<Query, Error> {
        Ok(Query {
            tuple: try_into_vec(tuple)?,
            formula: formula.try_into()?,
        })
    }
}

impl<'a> TryFrom<&'a Term<'a>> for Expression<'a> {
    type Error = Error<'a>;

    fn try_from(term: &'a Term<'a>) -> Result<Expression, Error> {
        match term {
            Term::Const(val) => Ok(Expression::Const(val)),
            Term::Var(name) => Ok(Expression::Var(name)),
            Term::Abs(..) => Err(Error::NotExpression(term)),
            Term::App(fun, _) if ops::kind(fun) == Some(Kind::Formula) => {
                Err(Error::NotExpression(term))
            }
            Term::App(fun, args) => {
                Ok(Expression::App(fun, try_into_vec(args)?))
            }
        }
    }
}

impl<'a> TryFrom<&'a Term<'a>> for Formula<'a> {
    type Error = Error<'a>;

    fn try_from(term: &'a Term<'a>) -> Result<Formula, Error> {
        match term {
            Term::Const(..) | Term::Var(..) => Err(Error::NotFormula(term)),
            Term::Abs(vars, box body) => {
                Ok(Formula::Exists(vars.clone(), box body.try_into()?))
            }
            // The Term::App arm has to be split to please the borrow checker,
            // since we move the term into the error.
            Term::App(fun, _) if ops::kind(fun) == Some(Kind::Expression) => {
                Err(Error::NotFormula(term))
            }
            Term::App(fun, args) => match ops::kind(fun) {
                Some(Kind::Formula) => match *fun {
                    ops::NOT => try_into_box(Formula::Not, args),
                    ops::AND => try_into_box_2(Formula::And, args),
                    ops::OR => try_into_box_2(Formula::Or, args),
                    ops::EQ => try_into_box_2(Formula::Equal, args),
                    _ => Ok(Formula::Pred(fun, try_into_vec(args)?)),
                },
                _ => Ok(Formula::Rel(fun, try_into_vec(args)?)),
            },
        }
    }
}

impl<'a> From<&'a Query<'a>> for ulc::Query<'a> {
    fn from(Query { tuple, formula }: &'a Query<'a>) -> ulc::Query {
        ulc::Query {
            tuple: into_vec(tuple),
            formula: formula.into(),
        }
    }
}

impl<'a> From<&'a Expression<'a>> for Term<'a> {
    fn from(expr: &'a Expression<'a>) -> Term {
        match expr {
            Expression::Const(val) => Term::Const(val),
            Expression::Var(name) => Term::Var(name),
            Expression::App(fun, args) => Term::App(fun, into_vec(args)),
        }
    }
}

impl<'a> From<&'a Formula<'a>> for Term<'a> {
    fn from(formula: &'a Formula<'a>) -> Term {
        match formula {
            Formula::Rel(fun, args) | Formula::Pred(fun, args) => {
                Term::App(fun, into_vec(args))
            }
            Formula::Equal(box lhs, box rhs) => {
                Term::App(ops::EQ, vec![lhs.into(), rhs.into()])
            }
            Formula::Not(box arg) => Term::App(ops::NOT, vec![arg.into()]),
            Formula::And(box lhs, box rhs) => {
                Term::App(ops::AND, vec![lhs.into(), rhs.into()])
            }
            Formula::Or(box lhs, box rhs) => {
                Term::App(ops::OR, vec![lhs.into(), rhs.into()])
            }
            Formula::Exists(vars, box body) => {
                Term::Abs(vars.clone(), box body.into())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::iter::once;

    #[test]
    fn free_vars_const() {
        assert_eq!(Expression::Const("x").free_vars(), HashSet::new());
    }

    #[test]
    fn free_vars_var() {
        assert_eq!(Expression::Var("x").free_vars(), once("x").collect());
    }

    #[test]
    fn free_vars_app() {
        assert_eq!(
            Expression::App(
                "f",
                vec![
                    Expression::Var("x"),
                    Expression::Var("x"),
                    Expression::Var("y"),
                ]
            ).free_vars(),
            vec!["x", "y"].into_iter().collect()
        );
    }

    #[test]
    fn free_vars_exists() {
        assert_eq!(
            Formula::Exists(
                vec!["x", "y"],
                box Formula::Rel(
                    "r",
                    vec![
                        Expression::Var("x"),
                        Expression::Var("y"),
                        Expression::Var("z"),
                    ]
                )
            ).free_vars(),
            once("z").collect()
        )
    }

    #[test]
    fn const_to_const_expr() {
        assert_eq!(Term::Const("x").try_into(), Ok(Expression::Const("x")));
    }

    #[test]
    fn var_to_var_expr() {
        assert_eq!(Term::Var("x").try_into(), Ok(Expression::Var("x")));
    }

    #[test]
    fn app_to_app_expr() {
        assert_eq!(
            Term::App("f", vec![Term::Var("x")]).try_into(),
            Ok(Expression::App("f", vec![Expression::Var("x")]))
        );
    }

    #[test]
    fn app_to_rel() {
        assert_eq!(
            Term::App("r", vec![Term::Var("x")]).try_into(),
            Ok(Formula::Rel("r", vec![Expression::Var("x")]))
        );
    }

    #[test]
    fn app_to_pred() {
        assert_eq!(
            Term::App("<", vec![Term::Var("x"), Term::Var("y")]).try_into(),
            Ok(Formula::Pred(
                "<",
                vec![Expression::Var("x"), Expression::Var("y")]
            ))
        );
    }

    #[test]
    fn app_to_equal() {
        assert_eq!(
            Term::App("=", vec![Term::Var("x"), Term::Var("y")]).try_into(),
            Ok(Formula::Equal(
                box Expression::Var("x"),
                box Expression::Var("y")
            ))
        );
    }

    #[test]
    fn app_to_not() {
        assert_eq!(
            Term::App("!", vec![Term::App("r", vec![Term::Var("x")])])
                .try_into(),
            Ok(Formula::Not(box Formula::Rel(
                "r",
                vec![Expression::Var("x")]
            )))
        );
    }

    #[test]
    fn abs_to_exists() {
        assert_eq!(
            Term::Abs(
                vec!["x"],
                Box::new(Term::App("r", vec![Term::Var("x")]))
            ).try_into(),
            Ok(Formula::Exists(
                vec!["x"],
                Box::new(Formula::Rel("r", vec![Expression::Var("x")]))
            ))
        );
    }

    #[test]
    fn not_expression() {
        let result: Result<Expression, Error> =
            Term::Abs(vec!["x"], Box::new(Term::Const("x"))).try_into();
        match result {
            Err(Error::NotExpression(..)) => (),
            _ => panic!(),
        }
    }

    #[test]
    fn not_formula() {
        let result: Result<Formula, Error> = Term::App("+", vec![]).try_into();
        match result {
            Err(Error::NotFormula(..)) => (),
            _ => panic!(),
        }
    }

    #[test]
    fn const_to_const_term() {
        let term: Term = Expression::Const("x").into();
        assert_eq!(term, Term::Const("x"));
    }

    #[test]
    fn var_to_var_term() {
        let term: Term = Expression::Var("x").into();
        assert_eq!(term, Term::Var("x"));
    }

    #[test]
    fn and_to_app() {
        let term: Term = Formula::And(
            box Formula::Rel("r", vec![Expression::Var("x")]),
            box Formula::Pred("q", vec![Expression::Const("y")]),
        ).into();
        assert_eq!(
            term,
            Term::App(
                "&",
                vec![
                    Term::App("r", vec![Term::Var("x")]),
                    Term::App("q", vec![Term::Const("y")]),
                ]
            )
        );
    }
}
