//! Library for converting from the tuple relational calculus to SQL.

#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(match_default_bindings)]
#![feature(nll)]
#![feature(slice_patterns)]
#![feature(try_from)]

#[macro_use]
extern crate lazy_static;

pub mod parser;

mod map;
mod ops;
mod sql;
mod trc;
mod ulc;
mod util;
