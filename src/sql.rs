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

/// A SQL query.
pub struct Query<'a> {
    /// The tuple of terms to select (empty means `*`).
    pub tuple: Vec<Expression<'a>>,
    /// The table to select from.
    pub table: &'a str,
    /// A list of join clauses (table name and "ON" condition).
    pub joins: Vec<Join<'a>>,
    /// The "WHERE" clause of the query.
    pub cond: Formula<'a>,
}

/// Kinds of SQL joins.
pub enum JoinKind {
    /// Inner join.
    Inner,
    /// Left join.
    Left,
    /// Right join.
    Right,
}

/// A SQL join clause.
pub struct Join<'a> {
    /// The kind of join.
    pub kind: JoinKind,
    /// The table to join to.
    pub table: &'a str,
    /// The "ON" clause.
    pub cond: Formula<'a>,
}

/// A means of referring to tables in a query by number.
pub enum Table {
    /// The table specified in the "FROM" clause.
    Primary,
    /// One of the joined tables, identified by a zero-based index.
    Joined(u32),
}

/// An expression in a SQL query.
pub enum Expression<'a> {
    /// A string constant.
    Const(&'a str),
    /// A table column, identified by a zero-based index.
    Col(Table, u32),
    /// A function applied to a tuple of terms.
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

pub enum Error<'a> {
    Foo(&'a str),
}

impl<'a> TryFrom<trc::Query<'a>> for Query<'a> {
    type Error = Error<'a>;

    fn try_from(query: trc::Query) -> Result<Query, Error> {
        Err(Error::Foo(""))
    }
}

// params:
// prettyindenent / one line
// schema / numbered
// impl<'a> fmt::Display for Query<'a> {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         write!(f, "SELECT DISTINCT {}")
//     }
// }
