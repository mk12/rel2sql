//! Tuple relational calculus parser.

use nom::*;

named!(formula, delimited!(char!('{'), alphanumeric, char!('}')));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn test_foo() {
        let f = b"{nice}";
        assert_eq!(formula(f), IResult::Done(&[][..], &b"nice"[..]));
    }
}
