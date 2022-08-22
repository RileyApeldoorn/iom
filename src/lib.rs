//! Lazily evaluated monadic IO actions.

use std::{ io::{ Read, Result, Write }, path::Path, mem, fs };
use Inner::{ Eval, Pure, Done };

/// A chain of lazy, composable IO actions.
pub struct IO <O> (Inner<O>);

enum Inner <O> {
	Eval (Box<dyn Action<Output = O>>),
	Pure (O),
	Done,
}

/// Primitive for [`IO`]. This is the "unsafe", lower level interface that can be
/// abused (if it weren't for other safety precautions such as the `Context` being
/// private).
trait Action {
    /// The value the action will evaluate to.
	type Output;
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

/// Thunks can be used to create actions without too much hassle.
impl<F, O> Action for F where F: FnMut () -> Result<IO<O>> {
	type Output = O;
	fn perform (&mut self, cx: Context<'_>) -> Result<Self::Output> {
    	// Evaluate the thunk
    	let IO (mut action) = self()?;
    	action.perform(cx)
	}
}

impl<T> Action for Inner<T> {
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

impl IO<()> {
    /// Perform the IO action.
    ///
    /// Note that this is a static associated function, not a method.
	pub fn run (IO (inner): IO<()>) -> Result<()> {
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
	pub fn capture (IO (inner): IO<()>) -> Result<String> {
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
impl<O> IO<O> {

    /// Perform a monadic binding operation. For the IO monad, this
    /// means simply sequencing `self` to happen before calling `f`
    /// on the result and then performing the value returned from
    /// `f`.
	pub fn bind <R> (self, f: impl FnOnce (O) -> IO<R> + 'static) -> IO<R>
	where
    	O: 'static,
        R: 'static,
    {
    	// Declare a new struct that holds the captured values
		struct Bind <A, F> (IO<A>, Option<F>);

		impl<A, F, X> Action for Bind<A, F>
		where
    		F: FnOnce (A) -> IO<X>,
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
	pub fn map <R> (self, f: impl FnOnce (O) -> R + 'static) -> IO<R>
	where
    	O: 'static,
    	R: 'static,
    {
		self.bind(|x| pure(f(x)))
	}

	/// Replace the value currently in the monad with a new `value`, discarding
	/// the old one.
	pub fn replace <R> (self, value: R) -> IO<R>
	where
    	O: 'static,
    	R: 'static,
    {
		self.map(|_| value)
	}

	/// Perform `self` and discard the output, then perform `other` and return
	/// its output.
	pub fn then <R> (self, other: IO<R>) -> IO<R>
	where
    	O: 'static,
    	R: 'static,
    {
		self.bind(|_| other)
    }

	/// Sequence `other` after `self`, but ignore its output and return `self`'s
	/// output instead.
	pub fn ignoring <R> (self, other: IO<R>) -> IO<O>
	where
    	O: 'static,
    	R: 'static,
	{
    	self.bind(|v| other.replace(v))
	}

    pub (crate) fn new (
        action: impl Action<Output = O> + 'static
    ) -> IO<O> {
		IO (Eval (Box::new(action)))
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
pub fn pure <T> (value: T) -> IO<T> {
    IO (Pure (value))
}

/// Ignore the output value of `x`.
pub fn void <T> (x: IO<T>) -> IO<()>
where
    T: 'static
{
	x.replace(())
}

/// Print a line to stdout.
pub fn println (s: impl ToString) -> IO<()> {
	struct PrintLn (String);

	impl Action for PrintLn {
		type Output = ();
		fn perform (&mut self, Context { o, .. }: Context<'_>) -> Result<Self::Output> {
    		writeln!(o, "{}", self.0)
		}
	}
    
	IO::new(PrintLn (s.to_string()))
}

/// Read a file's contents into a string.
pub fn read_file (path: impl AsRef<Path> + 'static) -> IO<String> {
    let mut p = Some (path);
	IO::new(move || {
    	let p = p.take().expect("Re-evaluation of IO action!");
		let s = fs::read_to_string(p)?;
		Ok (pure (s))
	})
}

/// Acquire a resource and apply a function to it.
pub fn bracket <I, O, F> (
    acquire: IO<I>,
    release: IO<()>,
) -> impl FnOnce (F) -> IO<O>
where
    F: FnOnce (I) -> IO<O> + 'static,
    I: 'static,
{
    struct Bracket <X, G> (IO<X>, IO<()>, Option<G>);

	impl<X, G, Y> Action for Bracket<X, G>
	where
    	G: FnOnce (X) -> IO<Y>
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
