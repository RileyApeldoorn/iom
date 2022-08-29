//! Defines an iterator extension trait.

use crate::{ IO, Context, void, Action, IsIO };
use std::io::Result;

/// Extends [`Iterator`]s with methods that are useful for interacting
/// with sets of [`IO`] instances.
pub trait IterExtIO<'a, T>: Iterator<Item = T> + Sized + 'a
where
    T: 'a,
{

    /// Construct an [`IO`] that, when evaluated, performs each action
    /// in sequence and discards the results.
	fn do_each <U> (self) -> IO<'a>
	where
    	T: IsIO<'a, U>,
    	U: 'a,
    {
    	IO::from_fn (move |Context { i, o, e }| {
        	self.map(T::into_io)
            	.map(void)
            	.map(|IO (mut a)| {
                	a.perform(Context { i, o, e })
            	})
            	.collect::<Result<_>>()
    	})
	}

	/// Apply `f` to each item in the iterator to transform it into
	/// an [`IO`] action. This produces a single folded `IO` that
	/// will perform all the created actions and discard the results.
	fn for_io <F, U, V> (self, f: F) -> IO<'a>
	where
    	F: FnMut (T) -> U + 'a,
    	U: IsIO<'a, V>,
    	V: 'a,
    {
        self.map(f).do_each()
    }

	/// Do a left-to-right monadic fold.
	///
	/// TODO document this lmao
    fn fold_io <B, F, O> (self, init: B, mut f: F) -> IO<'a, B>
    where
        F: FnMut (B, T) -> O + 'a,
        O: IsIO<'a, B>,
        B: 'a,
    {
        IO::from_fn (move |Context { i, o, e }| {
            let mut acc = init;
            for x in self {
                let IO (mut a) = f(acc, x).into_io();
                acc = a.perform(Context { i, o, e })?
            }
            Ok (acc)
        })
    }

}

impl<'a, T, I> IterExtIO<'a, T> for I
where
    I: Sized + Iterator<Item = T> + 'a,
    T: 'a,
{}
