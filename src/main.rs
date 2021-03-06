//! Program that converts tuple relational calculus to SQL.

extern crate rel2sql;

use rel2sql::parser::parse_Query;

fn main() {
    let res = parse_Query(
        "{(x):(exists y.R(x)<=(f(q)=n)|!Q(x,y)&!z())&p(1*(2+2)*3)}",
    );
    // let res = parse_Query("{(x,y,z):'12'}");
    println!("hi: {:?}", res);
    if let Ok(q) = res {
        println!("OK:\n{}", q);
    }
}
