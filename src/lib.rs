//! Library for working with the tuple relational calculus and SQL.

#![feature(const_fn)]
#![feature(match_default_bindings)]

pub mod parser;

mod sql;
mod trc;
mod ulc;
