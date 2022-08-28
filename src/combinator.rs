//! Useful combinators for handling and interacting with [`IO`]
//! computations.

use std::{io::Read, fmt::Display};

use super::{ IO, Context, Action, pure };

/// Map the output of `x` to `()`.
///
/// When the returned [`IO`] is performed, `x` will still be
/// evaluated, but its output will be discarded.
///
/// ```
/// use iom::{ pure, void, IO };
///
/// # fn main () -> std::io::Result<()> {
/// // Passing this to `IO::run` would be invalid...
/// let meow: IO<'_, &str> = pure("meow");
/// // This *can* be executed, though.
/// let action: IO<'_, ()> = void(meow);
///
/// IO::run(action)?;
/// # Ok (()) }
/// ```
///
/// `void(x)` is equivalent to `x.map(|_| ())` or `x.replace(())`.
pub fn void <'a, T> (x: IO<'a, T>) -> IO<'a>
where
    T: 'a,
{
    x.replace(())
}

/// Return a function that, given another function, returns a chain of
/// [`IO`] actions that are performed between performing `acquire` and
/// `release`.
///
/// # Example
///
/// In the example below, `the_bracket` is a function that takes a
/// function that takes `()` (since `println` returns `()`) and returns
/// an instance of `IO`. Whatever that action is, the bracket we construct
/// here guarantees that, before we run it, the message "start" will be
/// printed, and after it has finished running, "finish" will be printed.
/// ```
/// use iom::{ println, bracket, IO };
///
/// # fn main () -> std::io::Result<()> {
/// let the_bracket = bracket(println("start"), println("finish"));
/// let action = the_bracket(|_| {
///     println("busy...")
/// });
///
/// let result = IO::capture(action)?;
///
/// assert_eq!(result, "start\nbusy...\nfinish\n");
/// # Ok (()) }
/// ```
pub fn bracket <'a, I, T, F> (
    acquire: IO<'a, I>,
    release: IO<'a>,
) -> impl FnOnce (F) -> IO<'a, T>
where
    F: FnOnce (I) -> IO<'a, T> + 'a,
    T: 'a,
    I: 'a,
{
    // Set up the state.
    let IO (mut acquire) = acquire;
    let IO (mut release) = release;

    |f: F| IO::from_fn(move |Context { i, o, e }| {

        // Acquire the resource.
        let x = acquire.perform(Context { i, o, e })?;
        // Apply the function to the resource.
        let IO (mut a) = f(x);

        // Perform the effect but do not return early if it fails
        // since we still need to do cleanup.
        let result = a.perform(Context { i, o, e });
        // Perform cleanup.
        release.perform(Context { i, o, e })?;

        // Return the result of the action resulting from
        // the application of `f` to the resource.
        result

    })

}

/// Various combinators on the IO monad.
impl<'a, T> IO<'a, T>
where
    T: 'a,
{

    /// Perform a monadic binding operation. For the IO monad, this
    /// means performing `self`, calling `f` on the result and then
    /// performing the [`IO`] actions returned from `f`.
    ///
    /// You can think of this as the [`IO`] version of [`Option`]'s
    /// [`and_then`](Option::and_then) function, except fully lazy.
    ///
    /// If we simplify the signatures somewhat, the similarities are
    /// clear(er) to see:
    ///
    /// ```text
    /// fn and_then <F, U> (self: Option<T>, f: F) -> Option<U>
    /// where
    ///     F: FnOnce (T) -> Option<U>;
    ///
    /// fn bind <F, U> (self: IO<T>, f: F) -> IO<U>
    /// where
    ///     F: FnOnce (T) -> IO<U>;
    /// ```
    ///
    /// Just like how `Option`'s `and_then` merges the result of calling
    /// the given function into the existing value, `IO`'s `bind` does the
    /// same.
    ///
    /// The difference is in the merging strategy. In the case of `bind`,
    /// a new `IO` action is created that, when performed, first performs
    /// `self` and then uses the value produced by that, called `O` here,
    /// as an input to the given function, `f`. This in turn returns another
    /// instance of `IO`, which is performed immediately afterwards.
    ///
    /// A similar, albeit much less 'powerful' version of this combinator,
    /// is [`map`][Self::map]. It does not perform this merging step, but
    /// instead composes a function at the end of the chain.
    pub fn bind <U, F> (self, f: F) -> IO<'a, U>
    where
        F: FnOnce (T) -> IO<'a, U> + 'a,
        U: 'a,
    {
        // Prepare the state.
        let IO (mut a) = self;

        IO::from_fn(move |Context { i, o, e }| {

            // Perform the first action in order to get the input to
            // the function.
            let x = a.perform(Context { i, o, e })?;

            // Call the function and extract the wrapped inner value.
            let IO (mut a) = f(x);

            // Perform the returned action.
            a.perform(Context { i, o, e })

        })
    }

    /// Apply a function to an immutable reference of the output value
    /// to produce some sort of side effect. This effect is then also
    /// performed before the original output value is returned.
    ///
    /// This can be useful for debugging, for example:
    ///
    /// ```
    /// use iom::{ IO, pure, debug, void };
    ///
    /// # fn main () -> std::io::Result<()> {
    /// #[derive(Debug)]
    /// enum Greeting { Hello, Meow }
    ///
    /// let chain = pure(Greeting::Meow)
    ///     .tap(debug)
    ///     .replace(Greeting::Hello)
    ///     .tap(debug);
    ///
    /// let result = IO::capture(void(chain))?;
    ///
    /// assert_eq!(result, "Meow\nHello\n");
    /// # Ok (()) }
    /// ```
    pub fn tap <F> (self, f: F) -> IO<'a, T>
    where 
        F: for<'b> FnOnce (&'b T) -> IO<'b> + 'a,
    {
        // Prepare the state.
        let IO (mut a) = self;

        IO::from_fn(move |Context { i, o, e }| {
            let x = a.perform(Context { i, o, e })?;
            f(&x).0.perform(Context { i, o, e })?;
            Ok (x)
        })
    }

    /// Like [`tap`](IO::tap), but "impure": its side effects happen
    /// outside of the [`IO`] monad. This has some niche uses, for
    /// example [`trace`](IO::trace) is implemented in terms of
    /// `tap_impure`.
    pub fn tap_impure <F> (self, f: F) -> IO<'a, T>
    where
        F: for<'b> FnOnce (&'b T) + 'a,
    {
        self.tap(|x| pure(f(x)))
    }

    /// Write `msg` to stderr *directly*, leaving the value untouched.
    ///
    /// The value written to stderr will *not* be captured in any way.
    ///
    /// ```
    /// use iom::{ IO, empty };
    ///
    /// # fn main () -> std::io::Result<()> {
    /// let chain = empty.trace("I'm").trace("spamming");
    /// let result = IO::capture(chain)?;
    ///
    /// assert!(result.is_empty());
    /// # Ok (()) }
    /// ```
    pub fn trace (self, msg: impl Display + 'a) -> IO<'a, T> {
        self.tap_impure(move |_| {
            // Bypass the IO monad altogether when writing to stderr.
            // This makes it so the message cannot be captured.
            eprintln!("{msg}")
        })
    }

    /// Apply a function to the wrapped value.
    ///
    /// `map` on [`IO`] behaves similar to [`Option::map`], [`Result::map`]
    /// or [`Iterator::map`]. After this IO action is performed, its result
    /// is passed to the closure `f` and its output is then returned.
    pub fn map <U, F> (self, f: F) -> IO<'a, U>
    where
        F: FnOnce (T) -> U + 'a,
        U: 'a,
    {
        self.bind(|x| pure(f(x)))
    }

    /// Replace the value currently in the monad with a new `value`, discarding
    /// the old one.
    ///
    /// All actions are still performed. This is equivalent to `self.map(|_| value)`.
    pub fn replace <U> (self, value: U) -> IO<'a, U>
    where
        U: 'a,
    {
        self.map(|_| value)
    }

    /// Perform `self` and discard the output, then perform `other` and return
    /// its output.
    pub fn then <'b: 'a, U> (self, other: IO<'a, U>) -> IO<'a, U>
    where
        U: 'b,
    {
        self.bind(|_| other)
    }

    /// Perform `other` after `self`, but ignore its output and return `self`'s
    /// output instead.
    pub fn discard <U> (self, other: IO<'a, U>) -> IO<'a, T>
    where
        U: 'a,
    {
        self.bind(|v| other.replace(v))
    }

    /// Read `self`'s output and pass it to the closure `f`.
    ///
    /// ```
    /// use iom::{ IO, println, pure, empty };
    ///
    /// # fn main () -> std::io::Result<()> {
    /// // `b"meow"` is an array of chars, so it
    /// // does not implement `Read`.
    /// let buf = b"meow".as_ref();
    /// let a = pure(buf).with_content(|s| {
    ///     assert_eq!(s, "meow");
    ///     empty
    /// });
    ///
    /// IO::run(a)?;
    /// # Ok (()) }
    /// ```
    pub fn with_content <U, F> (self, f: F) -> IO<'a, U>
    where
        F: FnOnce (String) -> IO<'a, U> + 'a,
        T: Read,
        U: 'a,
    {
        self.bind(|mut r| IO::from_fn(move |cx| {

            // Read into a string buffer.
            let mut buf = String::new();
            r.read_to_string(&mut buf)?;

            // Apply `f` and extract the returned
            // action so we can perform it.
            let IO (mut a) = f(buf);
            a.perform(cx)

        }))
    }

}
