//! Program that converts tuple relational calculus to SQL.

extern crate rel2sql;

use rel2sql::parser::parse_Query;

fn main() {
    println!("hi: {:?}", parse_Query("{(x):R(x)&Q(x,y)}"));
}
