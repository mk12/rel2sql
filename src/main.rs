//! Program that converts tuple relational calculus to SQL.

extern crate rel2sql;

use rel2sql::parser::parse_Query;

fn main() {
    let res = parse_Query("{(x):(exists y.R(x)|!Q(x,y)&!z())&p(1*(2+2)*3)}");
    println!("hi: {:?}", res);
    if let Ok(q) = res {
        println!("OK:\n{}", q);
    }
}
