//! Syntactic operators.

use std::fmt;

/// .
trait Precedence {
    /// .
    fn precedence(&self) -> u32;
}

/// .
fn write_operation<T>(
    f: &mut fmt::Formatter,
    op: &str,
    args: &[T],
) -> fmt::Result
where
    T: fmt::Display + Precedence,
{
    match args {
        [arg] => {
            if arg.precedence() >=
        }
    }
}
