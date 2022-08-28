//! Primitives for constructing instances of [`IO`].

use std::{ fmt::{ Display, Debug }, path::Path, fs };

use super::{ IO, Inner::* };

/// An alias for `pure(())`, but with a `'static` lifetime.
#[allow(non_upper_case_globals)]
pub const empty: IO<'static> = IO (Pure (()));

/// Wrap a value in the monad without attaching any side effects.
///
/// ```
/// use iom::{ pure, println, IO };
///
/// # fn main () -> std::io::Result<()> {
/// // Prepare a IO action that prints something
/// let action = pure("meow").bind(println);
/// // Run the action
/// let result = IO::capture(action)?;
///
/// assert_eq!(result, "meow\n");
/// # Ok (()) }
/// ```
///
/// This can be useful in situations where you may want to do something
/// only if a condition holds true, for example:
///
/// ```
/// use iom::{ pure, println, IO };
///
/// # fn main () -> std::io::Result<()> {
/// // Prepare a IO action that returns code 0 if the input was "meow",
/// // and if the input was something else, it prints a message and
/// // returns 1.
/// let f = |s| -> IO<'_, usize> {
///     if s == "meow" {
///         pure(0)
///     } else {
///         let msg = format!("Expected 'meow', got {s}");
///         println(msg).map(|_| 1)
///     }
/// };
/// 
/// // The action needs to return `()` so we just print the
/// // value
/// let action = f("meow").bind(println);
/// 
/// // Run the action
/// let result: usize = IO::capture(action)?.trim().parse().unwrap();
///
/// assert_eq!(result, 0);
/// # Ok (()) }
/// ```
pub fn pure <'a, T> (value: T) -> IO<'a, T>
where
    T: 'a,
{
    IO (Pure (value))
}

/// Print a line to stdout.
pub fn println <'a> (s: impl Display + 'a) -> IO<'a> {
    IO::from_fn(move |cx| {
        writeln!(cx.o, "{s}")
    })
}

/// Print the debug representation of the given value to stdout.
pub fn debug <'a> (s: &'a impl Debug) -> IO<'a> {
    IO::from_fn(move |cx| {
        writeln!(cx.o, "{s:?}")
    })
}

/// Read a file's contents into a string.
pub fn read_file <'a> (p: impl AsRef<Path> + 'a) -> IO<'a, String> {
    IO::from_fn(|_| {
        fs::read_to_string(p)
    })
}
