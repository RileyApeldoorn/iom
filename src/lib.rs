//! Lazily evaluated monadic IO actions.

use std::{ io::{ Read, Result, Write }, mem, marker::PhantomData };
use Inner::{ Chain, Pure, Depleted };

mod combinator;
mod primitive;
mod iterext;

pub use combinator::*;
pub use primitive::*;
pub use iterext::*;

/// A chain of lazy, composable IO actions.
///
/// # Terminology
///
/// An instance of [`IO`] (also called an "action", "effect" or "chain" in these
/// docs) represents a future value yielded after zero or more side effects have
/// been performed. These effects generally interact with the real world in some
/// way.
///
/// For example, [`read_file`] returns `IO<String>`, which represents the result
/// of reading the contents of some file into a [`String`]. When `read_file`
/// returns, this effect has not yet happened. It only creates a [`Future`]-like
/// promise to do the effect as soon as it is evaluated/executed/performed.
///
/// Functions like [`read_file`] are referred to as "constructors" or "primitives"
/// of `IO`. They provide core building blocks for constructing more complicated
/// chains of delayed actions.
///
/// # Usage
///
/// `IO` provides two associated functions that can be used to perform the effects
/// represented by an instance: [`run`] and [`capture`]. Both of them only work on
/// `IO<()>`, mirroring the type of Haskell's `main`.
///
/// Performing `IO` using `run` will use the default stdin/stdout/stderr streams.
/// Effects like [`println()`] will write to stdout of the current process.
///
/// When executing using `capture`, on the other hand, the stdout will be captured
/// into a string and returned.
///
/// An example:
///
/// ```
/// use iom::{ IO, read_file, println, empty };
///
/// # fn main () -> std::io::Result<()> {
/// let action = read_file("test/data/hey.txt")
///     .bind(|s| {
///         assert_eq!("hey", s.trim());
///         empty
///     });
///
/// IO::run(action)?;
/// # Ok (()) }
/// ```
///
/// [`Future`]: std::future::Future
/// [`run`]: IO::run
/// [`capture`]: IO::capture
pub struct IO <'a, T = ()> (Inner<'a, T>);

/// The *actual* IO machinery.
enum Inner <'a, T> {
    /// One or more chained IO actions that have not been performed yet.
    Chain (Box<dyn Action<'a, Output = T> + 'a>),
    /// There are no side effects to perform (memory aid: pure = no side effects).
    Pure (T),
    /// The side effects have already been performed. If you encounter this
    /// variant, you should panic.
    Depleted,
}

/// Primitive for [`IO`]. This is the "unsafe", lower level interface that can be
/// abused (if it weren't for other safety precautions such as the [`Context`] being
/// private).
trait Action<'a> {
    /// The value the action will evaluate to after performing side effects.
    type Output: 'a;
    /// Attempts to perform an [`Action`] more than once is always cause for panic.
    /// Unfortunately due to the way trait objects work, this is impossible to express
    /// using move semantics.
    ///
    /// The solution is to hide the mutable-reference-shenanigans behind an
    /// interface that does use ownership. This interface is [`IO`]. If we need to
    /// take ownership of something within the library, generally the solution is
    /// to assume that any given [`Action`] is not performed more than once and
    /// diverge if this assumption turns out to be false.
    fn perform (&mut self, cx: Context<'_>) -> Result<Self::Output>;
}

impl<'a, T> Action<'a> for Inner<'a, T>
where
    T: 'a,
{
    type Output = T;
    fn perform (&mut self, cx: Context<'_>) -> Result<T> {
        match mem::replace(self, Depleted) {
            Chain (mut a) => a.perform(cx),
            Pure (v) => Ok (v),
            _ => panic!("Re-evaluation of IO action!"),
        }
    }
}

/// The execution context of an [`Action`], the primitive of [`IO`].
struct Context <'a> {
    /// Stdin
    i: &'a mut (dyn Read + Send + Sync),
    /// Stdout
    o: &'a mut (dyn Write + Send + Sync),
    /// Stderr
    e: &'a mut (dyn Write + Send + Sync),
}

/// Monads that an [`IO`] may be extracted from.
///
/// This is needed to get [`do_each`][IterExtIO::do_each] working.
pub trait IsIO<'a, T = ()>: 'a {

	/// Get the embedded IO computation.
	fn into_io (self) -> IO<'a, T>;

}

impl<'a, T> IsIO<'a, T> for IO<'a, T>
where
    T: 'a,
{
    #[inline(always)]
    fn into_io (self) -> IO<'a, T> { self }
}

impl IO<'_> {
    /// Perform the IO action.
    ///
    /// Note that this is a static associated function, not a method.
    pub fn run (IO (inner): IO<'_>) -> Result<()> {
        // Construct a new `Context` for the action.
        inner.run(Context {
            i: &mut std::io::stdin(),
            o: &mut std::io::stdout(),
            e: &mut std::io::stderr(),
        })
    }

    /// Perform the IO action and return anything printed to stdout
    /// as a string.
    ///
    /// This is a static associated function, so you have to call it like
    /// `IO::capture(action)` instead of `action.capture()`.
    pub fn capture (IO (inner): IO<'_>) -> Result<String> {
        // Construct a buffer that writes to `stdout` will
        // be written to.
        let mut buf = Vec::new();

        // Construct a new `Context` for the action.
        inner.run(Context {
            i: &mut std::io::stdin(),
            o: &mut buf,
            e: &mut std::io::stderr(),
        })?;

        // Convert the buffer into a `String` using
        // `&[u8]`'s `std::io::Read` impl.
        let mut s = String::with_capacity(buf.len());
        buf.as_slice().read_to_string(&mut s)?;

        Ok (s)
    }
}

impl Inner<'_, ()> {
    fn run (self, cx: Context<'_>) -> Result<()> {
        match self {
            Depleted | Pure (()) => Ok (()),
            Chain (mut action) => action.perform(cx)
        }
    }
}

/// Constructors for [`IO`].
impl<'a, T> IO<'a, T>
where
    T: 'a
{

    /// Wrap an [`Action`] in the [`IO`].
    pub (crate) fn new (
        action: impl Action<'a, Output = T> + 'a
    ) -> IO<'a, T> {
        IO (Chain (Box::new(action)))
    }

    /// Make it easier to define new relatively simple actions
    /// without all the boilerplate. Most actions are defined
    /// in terms of a closure, because that makes working out
    /// the types significantly easier (for us).
    pub (crate) fn from_fn (
        f: impl FnOnce (Context<'_>) -> Result<T> + 'a
    ) -> IO<'a, T> {
        struct FromFn <'x, F, O> (Option<F>, PhantomData<&'x O>);

        impl<'x, F, O> Action<'x> for FromFn<'x, F, O>
        where
            F: FnOnce (Context<'_>) -> Result<O> + 'x,
            O: 'x,
        {
            type Output = O;

            fn perform (&mut self, cx: Context<'_>) -> Result<Self::Output> {
                let FromFn (f, _) = self;

                // Ensure this is the first time the action is called.
                // This is required because `F` is `FnOnce` and not `FnMut`
                // and the borrow checker will complain about moving it if
                // we don't use `take` or something similar.
                let f = f.take().expect("Re-evaluation of IO action!");

                f(cx)
            }
        }

        IO::new(FromFn (Some (f), PhantomData))
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    /// Test whether [`bracket`] sequences actions correctly.
    fn bracket_sequences_actions_correctly () -> Result<()> {
        let using_bracket = {
            let first = println("first");
            let last  = println("last");
            bracket (first, last) (|_| {
                println("meow")
            })
        };

        let using_then = {
            let first  = println("first");
            let second = println("meow");
            let last   = println("last");
            first
                .then(second)
                .then(last)
        };

        let result_1 = IO::capture(using_bracket)?;
        let result_2 = IO::capture(using_then)?;

        assert_eq!(result_1, result_2);

        Ok (())
    }
}
