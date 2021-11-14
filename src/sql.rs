//! Structured Query Language (SQL).
//!
//! This module defines data structures for a limited form of SQL, and
//! implements conversion to it from the tuple relational calculus (see the
//! [`trc`] module). This conversion only succeeds if the query is range
//! restricted, which guarantees domain independence.
//!
//! [`trc`]: ../trc/index.html

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

pub struct Query<'a> {
    cols: Vec<Expression<'a>>,
    tables: Vec<Table<'a>>,
    joins: Vec<Join<'a>>,
    cond: Formula<'a>,
}

enum JoinKind {
    INNER,
    CROSS,
}

struct Join<'a> {
    kind: JoinKind,
    table: Table<'a>,
    cond: Formula<'a>,
}

struct Expression<'a> {}

struct Formula<'a> {}
