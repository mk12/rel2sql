//! Library for converting from the tuple relational calculus to SQL.

#![feature(match_default_bindings)]
#![feature(slice_patterns)]
#![feature(try_from)]

#[macro_use]
extern crate lazy_static;

pub mod parser;

mod ops;
mod sql;
mod trc;
mod ulc;
