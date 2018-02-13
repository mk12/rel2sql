//! Syntactic operators.
//!
//! This module defines built-in operators that should be recognized in the
//! relational calculus. It categorizes them, defines their precedences, and
//! implements a function for displaying them with minimal parenthesization.

use std::collections::HashMap;
use std::fmt;

/// Operator precedence (zero is lowest).
pub type Precedence = u32;

/// Kinds of operators.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Kind {
    /// A logical operator.
    Logic,
    /// A binary comparison operator.
    Comp,
    /// An arithmetic operator.
    Arith,
}

/// The lowest operator precedence, reserved for special use.
pub const LOWEST_PRECEDENCE: Precedence = 0;

/// The highest operator precedence, reserved for special use.
pub const HIGHEST_PRECEDENCE: Precedence = 8;

/// List of precedence tiers, in order of increasing precedence.
const PRECEDENCE_LIST: [&[&str]; (HIGHEST_PRECEDENCE - 1) as usize] = [
    &["|"],
    &["&"],
    &["=", "!="],
    &["<", "<=", ">", ">="],
    &["+", "-"],
    &["*", "/", "%"],
    &["!"],
];

/// List of operators organized by their kind.
const KIND_LIST: [(Kind, &[&str]); 3] = [
    (Kind::Logic, &["|", "&", "!"]),
    (Kind::Comp, &["=", "!=", "<", "<=", ">", ">="]),
    (Kind::Arith, &["+", "-", "*", "/", "%"]),
];

lazy_static! {
    /// A mapping from operators to their precedence.
    static ref PRECEDENCE_MAP: HashMap<&'static str, Precedence> = {
        let mut map = HashMap::new();
        for (i, &tier) in PRECEDENCE_LIST.iter().enumerate() {
            for &op in tier {
                map.insert(op, (i + 1) as Precedence);
            }
        }
        map
    };

    /// A mapping from operators to their kind.
    static ref KIND_MAP: HashMap<&'static str, Kind> = {
        let mut map = HashMap::new();
        for (kind, &ops) in KIND_LIST.iter() {
            for &op in ops {
                map.insert(op, *kind);
            }
        }
        map
    };
}

/// Returns the precedence of the operator, or None if it is not an operator.
pub fn precedence(op: &str) -> Option<Precedence> {
    PRECEDENCE_MAP.get(op).cloned()
}

/// Returns the kind of the operator, or None if it is not an operator.
pub fn kind(op: &str) -> Option<Kind> {
    KIND_MAP.get(op).cloned()
}

/// An expression that may need to be parenthesized.
pub trait Parenthesize {
    /// Returns the precedence of the expression.
    fn precedence(&self) -> Precedence;
}

/// Formats a unary or binary operation.
///
/// Writes the operation to `f`, where `op` is the operator and `prec` is its
/// precedence. The lenght of `args` must be either 1 (unary) or 2 (binary).
/// Writes spaces around binary operators, but not between unary operators and
/// their operands. Assumes all binary operators are left-associative.
pub fn write_operation<T>(
    f: &mut fmt::Formatter,
    op: &str,
    prec: Precedence,
    args: &[T],
) -> fmt::Result
where
    T: fmt::Display + Parenthesize,
{
    match args {
        [arg] => {
            if prec >= arg.precedence() {
                write!(f, "{}({})", op, arg)
            } else {
                write!(f, "{}{}", op, arg)
            }
        }
        [lhs, rhs] => match (prec > lhs.precedence(), prec >= rhs.precedence())
        {
            (false, false) => write!(f, "{} {} {}", lhs, op, rhs),
            (false, true) => write!(f, "{} {} ({})", lhs, op, rhs),
            (true, false) => write!(f, "({}) {} {}", lhs, op, rhs),
            (true, true) => write!(f, "({}) {} ({})", lhs, op, rhs),
        },
        _ => panic!("Invalid number of arguemnts"),
    }
}
