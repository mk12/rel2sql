//! Library for working with the tuple relational calculus and SQL.

#![feature(match_default_bindings)]
#![feature(slice_patterns)]
#![feature(try_from)]

#[macro_use]
extern crate quick_error;

pub mod parser;

mod ops;
mod sql;
mod trc;
mod ulc;
