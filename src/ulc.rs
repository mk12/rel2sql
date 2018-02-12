/// Untyped lambda calculus.

use std::fmt;

use ops;

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

/// A term in the untyped lambda calculus.
///
/// This representation is non-standard in a few ways:
///
/// 1. There are constants in addition to variables.
/// 2. Abstractions and applications are multi-argument.
/// 3. Applications can only have variable operators, not general terms.
#[derive(Debug, PartialEq, Eq)]
pub enum Term<'a> {
    /// A string constant.
    Const(&'a str),
    /// A named variable.
    Var(&'a str),
    /// A lambda abstraction with one or more bound variables.
    Abs(Vec<&'a str>, Box<Term<'a>>),
    /// An application of a named variable to a tuple of terms.
    App(&'a str, Vec<Term<'a>>),
}

/// Helper newtype for implementing `Display` on lists of items.
struct CommaSep<'a, T: 'a>(&'a [T]);

impl<'a, T> fmt::Display for CommaSep<'a, T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, item) in self.0.iter().enumerate() {
            if i != 0 {
                write!(f, ", ")?;
            }
            item.fmt(f)?
        }
        Ok(())
    }
}

impl<'a> fmt::Display for Query<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{({}) : {}}}", CommaSep(&self.tuple), self.formula)
    }
}

impl<'a> fmt::Display for Term<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Const(s) | Term::Var(s) => write!(f, "{}", s),
            Term::Abs(vars, body) => {
                write!(f, "exists {} . {}", CommaSep(vars), body)
            }
            Term::App(fun, args) => {
                if OPERATORS.contains(fun) {
                    write_op(f, fun, args)
                } else {
                    write!(f, "{}({})", fun, CommaSep(args))
                }
            }
        }
    }
}
