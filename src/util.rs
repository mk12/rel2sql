/// Miscellaneous utilities.

use std::convert::TryInto;

/// Converts a vector of type to another using `Into`.
pub fn vec_to_vec<'a, T, U>(v: Vec<T>) -> Vec<U>
where
    T: Into<U>,
{
    v.into_iter().map(Into::into).collect()
}

/// Converts a vector of type to another using `TryInto`.
///
/// Returns `Ok` if all elements convert successfully. Otherwise, returns the
/// `Err` for the first failed conversion.
pub fn try_vec_to_vec<'a, T, U, Error>(v: Vec<T>) -> Result<Vec<U>, Error>
where
    T: TryInto<U, Error = Error>,
{
    v.into_iter().map(TryInto::try_into).collect()
}

/// Converts a vector of one `T` to a `Box<U>`, and constructs `V` with it.
///
/// Returns `Err` if the vector has the wrong number of elements, or if
/// conversion from `T` to `U` using the `TryInto` trait fails.
pub fn try_vec_to_box<'a, T, U, V, F, Error>(
    make: F,
    args: Vec<T>,
) -> Result<V, Error>
where
    T: TryInto<U, Error = Error>,
    F: FnOnce(Box<U>) -> V,
    Error: From<&'static str>,
{
    let mut it = args.into_iter();
    match (it.next(), it.next()) {
        (Some(arg), None) => Ok(make(box arg.try_into()?)),
        _ => Err("Wrong number of arguments".into()),
    }
}

/// Converts a vector of two `T` to two `Box<U>`, and constructs `V` with them.
///
/// Returns `Err` if the vector has the wrong number of elements, or if
/// conversion from `T` to `U` using the `TryInto` trait fails.
pub fn try_vec_to_box_2<'a, T, U, V, F, Error>(
    make: F,
    args: Vec<T>,
) -> Result<V, Error>
where
    T: TryInto<U, Error = Error>,
    F: FnOnce(Box<U>, Box<U>) -> V,
    Error: From<&'static str>,
{
    let mut it = args.into_iter();
    match (it.next(), it.next(), it.next()) {
        (Some(arg1), Some(arg2), None) => {
            Ok(make(box arg1.try_into()?, box arg2.try_into()?))
        }
        _ => Err("Wrong number of arguments".into()),
    }
}