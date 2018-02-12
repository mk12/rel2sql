//! Tuple relational calculus.

use std::convert::{TryFrom, TryInto};

use ulc::{self, Term};

/// A query in the tuple relational calculus.
///
/// A query consists of a tuple and a formula. The answer to the query is the
/// value of the tuple under all valuations of free variables satisfying the
/// formula with respect to some database instance.
///
/// The lifetime 'a is the lifetime of all strings referenced in the query. This
/// makes it possible to avoid making any copies
#[derive(Debug, PartialEq, Eq)]
pub struct Query<'a> {
    /// The result tuple, usually containing Var expressions.
    pub tuple: Tuple<'a>,
    /// The query formula.
    pub formula: Formula<'a>,
}

/// A tuple of expressions.
type Tuple<'a> = Vec<Expression<'a>>;

/// An expression in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    /// A string constant.
    Const(&'a str),
    /// A named variable.
    Var(&'a str),
    /// A function applied to a tuple of expressions.
    App(&'a str, Tuple<'a>),
}

/// A formula in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula<'a> {
    /// A relation applied to a tuple of expressions.
    Rel(&'a str, Tuple<'a>),
    /// A predicate applied to a tuple of expressions.
    Pred(&'a str, Tuple<'a>),
    /// One or two formulas joined by a logical connective.
    Logic(Logic, Vec<Formula<'a>>),
    /// A formula exisentially quantified by a list of bound variables.
    Exists(Vec<&'a str>, Box<Formula<'a>>),
}

/// A logical connective.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Logic {
    /// Negation.
    Not,
    /// Conjunction.
    And,
    /// Disjunction.
    Or,
}

quick_error! {
    /// Error type for conversions to the tuple relational calculus.
    #[derive(Debug)]
    pub enum Error {
        NotExpression {}
        NotFormula {}
    }
}

/// Converts a vector of type `T` to a vector of type `U`.
///
/// Peforms the conversion using the `TryInto` trait. Returns `Ok` if all
/// elements convert successfully; otherwise, returns the first `Err`.
fn from_vec<T, U>(v: Vec<T>) -> Result<Vec<U>, Error>
where
    T: TryInto<U, Error = Error>,
{
    v.into_iter().map(TryInto::try_into).collect()
}

impl<'a> TryFrom<ulc::Query<'a>> for Query<'a> {
    type Error = Error;

    fn try_from(query: ulc::Query) -> Result<Query, Error> {
        Ok(Query {
            tuple: from_vec(query.tuple)?,
            formula: query.formula.try_into()?,
        })
    }
}

impl<'a> TryFrom<Term<'a>> for Expression<'a> {
    type Error = Error;

    fn try_from(term: Term) -> Result<Expression, Error> {
        match term {
            Term::Const(val) => Ok(Expression::Const(val)),
            Term::Var(name) => Ok(Expression::Var(name)),
            Term::Abs(..) => Err(Error::NotExpression),
            Term::App(fun, args) => Ok(Expression::App(fun, from_vec(args)?)),
        }
    }
}

impl<'a> TryFrom<ulc::Term<'a>> for Formula<'a> {
    type Error = Error;

    fn try_from(term: Term) -> Result<Formula, Error> {
        use self::Formula::{Exists, Logic, Pred, Rel};
        match term {
            Term::Const(..) => Err(Error::NotFormula),
            Term::Var(..) => Err(Error::NotFormula),
            Term::Abs(vars, body) => {
                let body: Formula = (*body as Term).try_into()?;
                Ok(Exists(vars, Box::new(body)))
            }
            Term::App(fun, args) => match fun.try_into() {
                Ok(Operator::Logic(op)) => Ok(Logic(op, from_vec(args)?)),
                Ok(Operator::Comp(op)) => Ok(Pred(op, from_vec(args)?)),
                Ok(Operator::Arith(..)) => Err(Error::NotFormula),
                Err(_) => Ok(Rel(fun, from_vec(args)?)),
            },
        }
    }
}

/// An operator used in expressions or formulas.
enum Operator<'a> {
    /// A logical connective.
    Logic(Logic),
    /// A numerical comparision operator.
    Comp(&'a str),
    /// An arithmetical operator.
    Arith(&'a str),
}

/// Arithmetic binary operators over expressions producing expressions.
const ARITH_OPERATORS: [&str; 5] = ["*", "/", "%", "+", "-"];

/// Comparison binary operators over expressions producing formulas.
const COMP_OPERATORS: [&str; 6] = ["=", "!=", "<", ">", "<=", ">="];

impl<'a> TryFrom<&'a str> for Operator<'a> {
    type Error = ();

    fn try_from(s: &str) -> Result<Operator, ()> {
        match s {
            "!" => Ok(Operator::Logic(Logic::Not)),
            "&" => Ok(Operator::Logic(Logic::And)),
            "|" => Ok(Operator::Logic(Logic::Or)),
            _ => {
                if ARITH_OPERATORS.contains(&s) {
                    Ok(Operator::Arith(s))
                } else if COMP_OPERATORS.contains(&s) {
                    Ok(Operator::Comp(s))
                } else {
                    Err(())
                }
            }
        }
    }
}

/*
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

/// Helper function to format application-like patterns.
fn write_app<T>(f: &mut fmt::Formatter, op: &str, args: &[T]) -> fmt::Result
where
    T: fmt::Display,
{
    write!(f, "{}({})", op, CommaSep(args))
}

impl<'a> fmt::Display for Query<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{{({}) : {}}}", CommaSep(&self.tuple), self.formula)
    }
}

impl<'a> fmt::Display for Expression<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Const(val) => write!(f, "{}", val),
            Expression::Var(name) => write!(f, "{}", name),
            Expression::App(fun, args) => {
                if ARITH_OPERATORS.contains(fun) {
                    FmtOperator(self).fmt(f)
                } else {
                    write_app(f, fun, args)
                }
            }
        }
    }
}

impl<'a> fmt::Display for Formula<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::Rel(rel, args) => write_app(f, rel, args),
            Formula::Pred(pred, args) => {
                write!(f, "{} {} {}", args[0], pred, args[1])
            }
            Formula::Logic(op, args) => FmtOperator(self).fmt(f),
            Formula::Exists(vars, body) => {
                write!(f, "exists {} . {}", CommaSep(vars), body)
            }
        }
    }
}

/// An interface for unary and binary operators.
trait Operator
where
    Self: Sized,
{
    /// Returns the symbol used for the operator.
    fn symbol(&self) -> &str;
    /// Returns true for unary operators and false for binary operators.
    fn unary(&self) -> bool;
    /// Returns the precedence of the operators (zero is highest).
    fn precedence(&self) -> u32;
    /// Returns the arguments to the operator expression.
    fn args(&self) -> &[Self];
}

impl<'a> Operator for Expression<'a> {
    fn symbol(&self) -> &str {
        if let Expression::App { fun, .. } = self {
            fun
        } else {
            ""
        }
    }

    fn unary(&self) -> bool {
        false
    }

    fn precedence(&self) -> u32 {
        match self {
            Expression::App { fun, .. } => match *fun {
                "+" | "-" => 2,
                "*" | "/" | " %" => 1,
                _ => 0,
            },
            _ => 0,
        }
    }

    fn args(&self) -> &[Expression<'a>] {
        if let Expression::App { args, .. } = self {
            args
        } else {
            &[]
        }
    }
}

impl<'a> Operator for Formula<'a> {
    fn symbol(&self) -> &str {
        match self {
            Formula::Conn { conn, .. } => match conn {
                Logic::Not => "!",
                Logic::And => "&",
                Logic::Or => "|",
            },
            _ => "",
        }
    }

    fn unary(&self) -> bool {
        if let Formula::Conn { conn, .. } = self {
            *conn == Logic::Not
        } else {
            false
        }
    }

    fn precedence(&self) -> u32 {
        match self {
            Formula::Exists { .. } => 4,
            Formula::Conn { conn, .. } => match conn {
                Logic::Or => 3,
                Logic::And => 2,
                Logic::Not => 1,
            },
            _ => 0,
        }
    }

    fn args(&self) -> &[Formula<'a>] {
        if let Formula::Conn { args, .. } = self {
            args
        } else {
            &[]
        }
    }
}

/// Helper newtype for implementing `Display` on operators.
struct FmtOperator<'a, T: 'a>(&'a T);

impl<'a, T> fmt::Display for FmtOperator<'a, T>
where
    T: fmt::Display + Operator,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op = &self.0;
        if op.unary() {
            let arg = &op.args()[0];
            if arg.precedence() >= op.precedence() {
                write!(f, "{}({})", op.symbol(), arg)
            } else {
                write!(f, "{}{}", op.symbol(), arg)
            }
        } else {
            let lhs = &op.args()[0];
            let rhs = &op.args()[1];
            let prec = op.precedence();
            let symbol = op.symbol();
            match (lhs.precedence() > prec, rhs.precedence() >= prec) {
                (false, false) => write!(f, "{} {} {}", lhs, symbol, rhs),
                (false, true) => write!(f, "{} {} ({})", lhs, symbol, rhs),
                (true, false) => write!(f, "({}) {} {}", lhs, symbol, rhs),
                (true, true) => write!(f, "({}) {} ({})", lhs, symbol, rhs),
            }
        }
    }
}


impl<'a> fmt::Display for Expression<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Const { val } => write!(f, "{}", val),
            Expression::Var { name } => write!(f, "{}", name),
            Expression::App { fun, args } => {
                if EXPRESSION_OPERATORS.contains(fun) {
                    FmtOperator(self).fmt(f)
                } else {
                    write_app(f, fun, args)
                }
            }
        }
    }
}

impl<'a> fmt::Display for Formula<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::App { pred, args } => {
                if FORMULA_OPERATORS.contains(pred) {
                    write!(f, "{} {} {}", args[0], pred, args[1])
                } else {
                    write_app(f, pred, args)
                }
            }
            Formula::Conn { conn, args } => FmtOperator(self).fmt(f),
            Formula::Exists { vars, body } => {
                write!(f, "exists {} . {}", CommaSep(vars), body)
            }
        }
    }
}


*/
