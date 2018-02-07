//! Tuple relational calculus data structures.

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
struct Query<'a> {
    /// The result tuple, usually containing Var expressions.
    tuple: Vec<Expression<'a>>,
    /// The query formula.
    formula: Formula<'a>,
}

/// Type of an expression in the tuple relational calculus.
///
/// This is only used for tagging constants for display purposes (for example,
/// text needs to be quoted). It is not used for typechecking.
enum Type {
    Number,
    Text,
}

/// An expression in the tuple relational calculus.
enum Expression<'a> {
    /// A constant expression.
    Const { value: &'a str, typ: Type },
    /// A variable expression.
    Var { name: &'a str },
    /// An application of an operator to expression arguments.
    App {
        op: &'a str,
        args: Vec<Expression<'a>>,
    },
}

/// A logical connective that can be used in a formula.
enum Connective {
    And,
    Or,
    Not,
}

/// A formula in the tuple relational calculus.
enum Formula<'a> {
    /// A formula denoting that the args tuple belongs to the named relation.
    Rel {
        name: &'a str,
        args: Vec<Expression<'a>>,
    },
    /// A combination of formulas joined by a logical connective.
    Conn {
        op: Connective,
        args: Vec<Formula<'a>>,
    },
    /// An application of a predicate to expression arguments.
    App {
        op: &'a str,
        args: Vec<Expression<'a>>,
    },
}
