//! Lazily evaluated monadic IO actions.

use std::{ io::{ Read, Result, Write }, path::Path, mem, fs, marker::PhantomData };
use Inner::{ Eval, Pure, Done };

/// A chain of lazy, composable IO actions.
pub struct IO <'a, O = ()> (Inner<'a, O>);

enum Inner <'a, O> {
    Eval (Box<dyn Action<'a, Output = O> + 'a>),
    Pure (O),
    Done,
}

/// Primitive for [`IO`]. This is the "unsafe", lower level interface that can be
/// abused (if it weren't for other safety precautions such as the `Context` being
/// private).
trait Action<'a> {
    /// The value the action will evaluate to.
    type Output: 'a;
    /// Attempts to perform an [`Action`] more than once is generally cause for
    /// panic. Unfortunately due to the way trait objects work, this is impossible
    /// to express using move semantics.
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
        match mem::replace(self, Done) {
            Eval (mut a) => a.perform(cx),
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

impl IO<'_> {
    /// Perform the IO action.
    ///
    /// Note that this is a static associated function, not a method.
    pub fn run (IO (inner): IO<'_>) -> Result<()> {
        // We only have to perform an action when `inner` is [`Eval`].
        let mut action = match inner {
            Done | Pure (_) => return Ok (()),
            Eval (action) => action,
        };

        // Construct a new `Context` for the action.
        action.perform(Context {
            i: &mut std::io::stdin(),
            o: &mut std::io::stdout(),
            e: &mut std::io::stderr(),
        })

    }

    /// Perform the IO action and return anything printed to stdout
    /// as a string.
    pub fn capture (IO (inner): IO<'_>) -> Result<String> {
        // We only have to perform an action when `inner` is [`Eval`].
        let mut action = match inner {
            Done | Pure (_) => return Ok ("".to_string()),
            Eval (action) => action,
        };

        let mut buf = Vec::new();

        // Construct a new `Context` for the action.
        action.perform(Context {
            i: &mut std::io::stdin(),
            o: &mut buf,
            e: &mut std::io::stderr(),
        })?;

        let mut s = String::with_capacity(buf.len());
        buf.as_slice().read_to_string(&mut s)?;
        Ok (s)
    }
}

/// Various combinators on the IO monad.
impl<'a, O> IO<'a, O>
where
    O: 'a
{

    pub (crate) fn new (
        action: impl Action<'a, Output = O> + 'a
    ) -> IO<'a, O> {
        IO (Eval (Box::new(action)))
    }

    /// Make it easier to define new relatively simple actions
    /// without all the boilerplate.
    pub (crate) fn from_fn (
        f: impl FnOnce (Context<'_>) -> Result<O> + 'a
    ) -> IO<'a, O> {
        struct FromFn <'x, F, O> (Option<F>, PhantomData<&'x O>);

        impl<'x,F, O> Action<'x> for FromFn<'x, F, O>
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

    /// Perform a monadic binding operation. For the IO monad, this
    /// means simply sequencing `self` to happen before calling `f`
    /// on the result and then performing the value returned from
    /// `f`.
    pub fn bind <R> (self, f: impl FnOnce (O) -> IO<'a, R> + 'a) -> IO<'a, R>
    where
        R: 'a,
    {
        // Declare a new struct that holds the captured values
        struct Bind <'c, A, F> (IO<'c, A>, Option<F>);

        impl<'c, 'd: 'c, A, F, X> Action<'d> for Bind<'c, A, F>
        where
            F: FnOnce (A) -> IO<'d, X> + 'd,
            F::Output: 'c,
            X: 'd,
            A: 'c,
        {
            type Output = X;

            fn perform (&mut self, Context { i, o, e }: Context<'_>) -> Result<Self::Output> {
                // Destructure `self` to get access to the captures
                let Bind (IO (a), f) = self;

                // Ensure this is the first time the action is called.
                // This is required because `F` is `FnOnce` and not `FnMut`
                // and the borrow checker will complain about moving it if
                // we don't use `take` or something similar.
                let f = f.take().expect("Re-evaluation of IO action!");

                // Perform the first action in order to get the input to
                // the function.
                let x = a.perform(Context { i, o, e })?;

                // Call the function and extract the wrapped inner value.
                let IO (mut a) = f(x);

                // Perform the returned action.
                a.perform(Context { i, o, e })
            }
        }

        // Return an instance of the custom struct wrapped in the
        // `IO` monad initialized with the captured values
        IO::new(Bind (self, Some (f)))
    }

    /// Apply a function to the wrapped value.
    pub fn map <R> (self, f: impl FnOnce (O) -> R + 'a) -> IO<'a, R>
    where
        O: 'static,
        R: 'static,
    {
        self.bind(|x| pure(f(x)))
    }

    /// Replace the value currently in the monad with a new `value`, discarding
    /// the old one.
    pub fn replace <R> (self, value: R) -> IO<'a, R>
    where
        O: 'static,
        R: 'static,
    {
        self.map(|_| value)
    }

    /// Perform `self` and discard the output, then perform `other` and return
    /// its output.
    pub fn then <R> (self, other: IO<'a, R>) -> IO<'a, R>
    where
        O: 'static,
        R: 'static,
    {
        self.bind(|_| other)
    }

    /// Sequence `other` after `self`, but ignore its output and return `self`'s
    /// output instead.
    pub fn ignoring <R> (self, other: IO<'a, R>) -> IO<'a, O>
    where
        O: 'static,
        R: 'static,
    {
        self.bind(|v| other.replace(v))
    }

}

/// Wrap a value in the monad.
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
pub fn pure <'a, T> (value: T) -> IO<'a, T> where T: 'a {
    IO (Pure (value))
}

/// Ignore the output value of `x`.
pub fn void <'a, T> (x: IO<'a, T>) -> IO<'a>
where
    T: 'static
{
    x.replace(())
}

/// Print a line to stdout.
pub fn println (s: impl ToString) -> IO<'static> {
    struct PrintLn (String);

    impl Action<'static> for PrintLn {
        type Output = ();
        fn perform (&mut self, Context { o, .. }: Context<'_>) -> Result<Self::Output> {
            writeln!(o, "{}", self.0)
        }
    }

    IO::new(PrintLn (s.to_string()))
}

/// Read a file's contents into a string.
pub fn read_file <'a> (path: impl AsRef<Path> + 'a) -> IO<'a, String> {
    let mut p = Some (path);
    IO::from_fn(move |_| {
        let p = p.take().expect("Re-evaluation of IO action!");
        let s = fs::read_to_string(p)?;
        Ok (s)
    })
}

/// Acquire a resource and apply a function to it.
pub fn bracket <'a, I, O, F> (
    acquire: IO<'a, I>,
    release: IO<'a>,
) -> impl FnOnce (F) -> IO<'a, O>
where
    F: FnOnce (I) -> IO<'a, O> + 'a,
    O: 'a,
    I: 'a,
{
    struct Bracket <'b, 'c, X, G> (IO<'b, X>, IO<'c>, Option<G>);

    impl<'b, 'c, 'd, X, G, Y> Action<'d> for Bracket<'b, 'c, X, G>
    where
        G: FnOnce (X) -> IO<'d, Y> + 'd,
        Y: 'd,
        X: 'b,
        'd: 'b,
        'd: 'c,
        G::Output: 'c,
    {
        type Output = Y;

        fn perform (&mut self, Context { i, o, e }: Context<'_>) -> Result<Self::Output> {
            // Get all the interesting values from `self`.
            let Bracket (IO (acquire), IO (release), f) = self;
            // `f` is always `Some` when it is constructed, so if it
            // is `None` that means someone is trying to evaluate IO
            // actions more than once, which *should* be impossible.
            let f = f.take().expect("Re-evaluation of IO action!");

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
        }
    }

    |f| IO::new(Bracket (acquire, release, Some (f)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    /// Test whether [`bracket`] sequences actions correctly.
    fn sequencing_bracket () {
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

        let result_1 = IO::capture(using_bracket).unwrap();
        let result_2 = IO::capture(using_then).unwrap();

        assert_eq!(result_1, result_2);
    }
}
