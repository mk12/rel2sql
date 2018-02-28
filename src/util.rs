/// Miscellaneous utilities.

use std::convert::TryInto;

/// Converts a slice of one type to another type using `Into`.
pub fn into_vec<'a, T, U>(v: &'a [T]) -> Vec<U>
where
    &'a T: Into<U>,
{
    v.iter().map(Into::into).collect()
}

/// Converts a slice of one type to another type using `TryInto`.
///
/// Returns `Ok` if all elements convert successfully. Otherwise, returns the
/// `Err` for the first failed conversion.
pub fn try_into_vec<'a, T, U, Error>(v: &'a [T]) -> Result<Vec<U>, Error>
where
    &'a T: TryInto<U, Error = Error>,
{
    v.iter().map(TryInto::try_into).collect()
}

/// Converts a slice of one `T` to a `Box<U>`, and constructs `V` with it.
///
/// Returns `Err` if the slice has the wrong number of elements, or if
/// conversion from `T` to `U` using the `TryInto` trait fails.
pub fn try_into_box<'a, T, U, V, F, Error>(
    make: F,
    args: &'a [T],
) -> Result<V, Error>
where
    &'a T: TryInto<U, Error = Error>,
    F: FnOnce(Box<U>) -> V,
    Error: From<&'static str>,
{
    let mut it = args.iter();
    match (it.next(), it.next()) {
        (Some(arg), None) => Ok(make(box arg.try_into()?)),
        _ => Err("Wrong number of arguments".into()),
    }
}

/// Converts a slice of two `T` to two `Box<U>`, and constructs `V` with them.
///
/// Returns `Err` if the slice has the wrong number of elements, or if
/// conversion from `T` to `U` using the `TryInto` trait fails.
pub fn try_into_box_2<'a, T, U, V, F, Error>(
    make: F,
    args: &'a [T],
) -> Result<V, Error>
where
    &'a T: TryInto<U, Error = Error>,
    F: FnOnce(Box<U>, Box<U>) -> V,
    Error: From<&'static str>,
{
    let mut it = args.iter();
    match (it.next(), it.next(), it.next()) {
        (Some(arg1), Some(arg2), None) => {
            Ok(make(box arg1.try_into()?, box arg2.try_into()?))
        }
        _ => Err("Wrong number of arguments".into()),
    }
}
