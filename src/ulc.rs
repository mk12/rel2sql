/// Untyped lambda calculus.

/// A term in the untyped lambda calculus.
///
/// This representation is non-standard in a few ways:
///
/// 1. There are constants in addition to variables.
/// 2. Abstractions and applications are multi-argument.
/// 3. Applications can only have variables on the left-hand side.
#[derive(Debug, PartialEq, Eq)]
pub enum Term<'a> {
    /// A string constant.
    Const(&'a str),
    /// A named variable.
    Var(&'a str),
    /// A lambda abstraction, with one or more bound variables.
    Abs(Vec<&'a str>, Box<Term<'a>>),
    /// An application of a named variable to a term.
    App(&'a str, Vec<Term<'a>>),
}

/// A lambda calculus representation of a relational calculus query.
///
/// This structure represents a tuple relation calculus query in the untyped
/// lambda calculus. It might not be well-formed, since the lambda calculus
/// makes no distinction between expressions and formulas.
#[derive(Debug, PartialEq, Eq)]
pub struct Query<'a> {
    /// The result tuple.
    pub tuple: Vec<Term<'a>>,
    /// The query formula.
    pub formula: Term<'a>,
}
