//! Tuple relational calculus.
//!
//! This module defines tuple relational calculus (TRC) data structures and
//! implements conversions to and from the untyped lambda calculus (see the
//! [`ulc`] module). The conversion from ULC can fail, since TRC distinguishes
//! formulas from terms, and recognizes predefined operators from the [`ops`]
//! module. Conversion back to ULC always succeeds.
//!
//! [`ulc`]: ../ulc/index.html
//! [`ops`]: ../ops/index.html

use std::convert::{TryFrom, TryInto};
use std::fmt;
use std::error;

use ops::{self, Kind, Logic};
use ulc::{self, Term};

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
    /// One or two formulas joined by a logical operator.
    Logic(Logic, Vec<Formula<'a>>),
    /// A formula exisentially quantified by a list of bound variables.
    Exists(Vec<&'a str>, Box<Formula<'a>>),
}

/// Error type for conversions to the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Error<'a> {
    /// Failure of a term to convert to an expression.
    NotExpression(Term<'a>),
    /// Failure of a term to convert to a formula.
    NotFormula(Term<'a>),
    /// An unexpected internal error.
    Internal,
}

impl<'a> error::Error for Error<'a> {
    fn description(&self) -> &str {
        match self {
            Error::NotExpression(..) => "Not an expression",
            Error::NotFormula(..) => "Not a formula",
            Error::Internal => "Internal error",
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
            Error::Internal => write!(f, "An internal error occurred"),
        }
    }
}

/// Converts a vector of type to another using `Into`.
fn vec_to_vec<'a, T, U>(v: Vec<T>) -> Vec<U>
where
    T: Into<U>,
{
    v.into_iter().map(Into::into).collect()
}

/// Converts a vector of type to another using `TryInto`.
///
/// Peforms the conversion using the `TryInto` trait. Returns `Ok` if all
/// elements convert successfully; otherwise, returns the first `Err`.
fn try_vec_to_vec<'a, T, U>(v: Vec<T>) -> Result<Vec<U>, Error<'a>>
where
    T: TryInto<U, Error = Error<'a>>,
{
    v.into_iter().map(TryInto::try_into).collect()
}

impl<'a> TryFrom<ulc::Query<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(query: ulc::Query) -> Result<Query, Error> {
        Ok(Query {
            tuple: try_vec_to_vec(query.tuple)?,
            formula: query.formula.try_into()?,
        })
    }
}

impl<'a> TryFrom<Term<'a>> for Expression<'a> {
    type Error = Error<'a>;

    fn try_from(term: Term) -> Result<Expression, Error> {
        match term {
            Term::Const(val) => Ok(Expression::Const(val)),
            Term::Var(name) => Ok(Expression::Var(name)),
            Term::Abs(..) => Err(Error::NotExpression(term)),
            Term::App(fun, args) => {
                Ok(Expression::App(fun, try_vec_to_vec(args)?))
            }
        }
    }
}

impl<'a> TryFrom<Term<'a>> for Formula<'a> {
    type Error = Error<'a>;

    fn try_from(term: Term) -> Result<Formula, Error> {
        match term {
            Term::Const(..) => Err(Error::NotFormula(term)),
            Term::Var(..) => Err(Error::NotFormula(term)),
            Term::Abs(vars, body) => {
                let body: Formula = (*body).try_into()?;
                Ok(Formula::Exists(vars, Box::new(body)))
            }
            // The Term::App arm has to be split to please the borrow checker,
            // since we move the term into the error.
            Term::App(fun, _) if ops::kind(fun) == Some(Kind::Arith) => {
                Err(Error::NotFormula(term))
            }
            Term::App(fun, args) => match ops::kind(fun) {
                Some(Kind::Logic) => {
                    let op = fun.parse().or(Err(Error::Internal))?;
                    Ok(Formula::Logic(op, try_vec_to_vec(args)?))
                }
                Some(Kind::Comp) => {
                    Ok(Formula::Pred(fun, try_vec_to_vec(args)?))
                }
                _ => Ok(Formula::Rel(fun, try_vec_to_vec(args)?)),
            },
        }
    }
}

impl<'a> From<Query<'a>> for ulc::Query<'a> {
    fn from(query: Query) -> ulc::Query {
        ulc::Query {
            tuple: vec_to_vec(query.tuple),
            formula: query.formula.into(),
        }
    }
}

impl<'a> From<Expression<'a>> for Term<'a> {
    fn from(expr: Expression) -> Term {
        match expr {
            Expression::Const(val) => Term::Const(val),
            Expression::Var(name) => Term::Var(name),
            Expression::App(fun, args) => Term::App(fun, vec_to_vec(args)),
        }
    }
}

impl<'a> From<Formula<'a>> for Term<'a> {
    fn from(formula: Formula) -> Term {
        match formula {
            Formula::Rel(fun, args) | Formula::Pred(fun, args) => {
                Term::App(fun, vec_to_vec(args))
            }
            Formula::Logic(op, args) => Term::App(op.into(), vec_to_vec(args)),
            Formula::Exists(vars, body) => {
                let body: Term = (*body).into();
                Term::Abs(vars, Box::new(body))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
            Term::App("=", vec![Term::Var("x"), Term::Var("y")]).try_into(),
            Ok(Formula::Pred(
                "=",
                vec![Expression::Var("x"), Expression::Var("y")]
            ))
        );
    }

    #[test]
    fn app_to_logic() {
        assert_eq!(
            Term::App("!", vec![Term::App("r", vec![Term::Var("x")])])
                .try_into(),
            Ok(Formula::Logic(
                Logic::Not,
                vec![Formula::Rel("r", vec![Expression::Var("x")])]
            ))
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
}
