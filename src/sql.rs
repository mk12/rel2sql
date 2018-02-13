//! Basic version of SQL (Structured Query Language).
//!
//! This module defines a limited form of SQL, and implements conversion to it
//! from the tuple relational calculus (see the [`trc`] module). This conversion
//! fails if the query is not range restricted (which guarantees domain
//! independence).
//!
//! [`trc`]: ../trc/index.html

use std::convert::{TryFrom, TryInto};
use std::fmt;

use trc;

/// A SQL query.
pub struct Query<'a> {
    /// The tuple of terms to select.
    pub tuple: Vec<Term<'a>>,
    /// The table to select from.
    pub table: &'a str,
    /// A list of join clauses (table name and "ON" condition).
    pub joins: Vec<Join<'a>>,
    /// The "WHERE" clause of the query.
    pub cond: Term<'a>,
}

/// Kinds of SQL joins.
pub enum JoinKind {
    /// Inner join, requiring a match from both sides.
    Inner,
    /// Left join,
    Left,
}

/// A SQL join clause.
pub struct Join<'a> {
    /// The kind of join.
    pub kind: JoinKind,
    /// The table to join to.
    pub table: &'a str,
    /// The "ON" clause.
    pub cond: Term<'a>,
}

/// .
pub enum Term<'a> {
    Foo(&'a str),
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
