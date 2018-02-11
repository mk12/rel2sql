//! Tuple relational calculus.

use std::fmt;

/// A query in the tuple relational calculus.
///
/// A query consists of a tuple and a formula. The answer to the query is the
/// set of all tuples satisfying the formula with respect to some database
/// instance. In a well-formed query, the free variables of the formula must be
/// a subset of the free variables in the result tuple.
///
/// The lifetime 'a is the lifetime of all strings referenced in the query. In
/// the case of parsing text input, this allows for referring directly into the
/// text without making any copies.
#[derive(Debug, PartialEq, Eq)]
pub struct Query<'a> {
    /// The result tuple, usually containing Var expressions.
    pub tuple: Tuple<'a>,
    /// The query formula.
    pub formula: Formula<'a>,
}

/// A tuple of expressions.
pub type Tuple<'a> = Vec<Expression<'a>>;

/// An expression in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    /// A constant expression.
    Const { val: &'a str },
    /// A variable expression.
    Var { name: &'a str },
    /// A function applied to a tuple of expressions.
    App { fun: &'a str, args: Tuple<'a> },
}

/// A formula in the tuple relational calculus.
#[derive(Debug, PartialEq, Eq)]
pub enum Formula<'a> {
    /// A predicate (possibly a relation) applied to a tuple of expressions.
    App { pred: &'a str, args: Tuple<'a> },
    /// A combination of formulas joined by a logical connective.
    Conn {
        conn: Connective,
        args: Vec<Formula<'a>>,
    },
    /// Existential quantification operator.
    Exists {
        vars: Vec<&'a str>,
        body: Box<Formula<'a>>,
    },
}

/// A logical connective that can be used in a formula.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Connective {
    Not,
    And,
    Or,
}

impl<'a> Query<'a> {
    fn is_range_restricted(&self) -> bool {
        true
    }
}

impl<'a> Expression<'a> {
    fn free_vars(&self) -> Vec<&str> {
        vec![]
    }
}

impl<'a> Formula<'a> {
    fn free_vars(&self) -> Vec<&str> {
        vec![]
    }
}

/// Binary operators over expressions producing expressions.
const EXPRESSION_OPERATORS: [&str; 5] = ["*", "/", "%", "+", "-"];

/// Binary operators over expressions producing formulas.
const FORMULA_OPERATORS: [&str; 6] = ["=", "!=", "<", ">", "<=", ">="];

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
                Connective::Not => "!",
                Connective::And => "&",
                Connective::Or => "|",
            },
            _ => "",
        }
    }

    fn unary(&self) -> bool {
        if let Formula::Conn { conn, .. } = self {
            *conn == Connective::Not
        } else {
            false
        }
    }

    fn precedence(&self) -> u32 {
        match self {
            Formula::Exists { .. } => 4,
            Formula::Conn { conn, .. } => match conn {
                Connective::Or => 3,
                Connective::And => 2,
                Connective::Not => 1,
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

/// Helper newtype for implementing `Display` on lists.
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
