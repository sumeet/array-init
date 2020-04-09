#![no_std]
#![allow(incomplete_features)]
#![feature(const_generics)]

//! The `array-init` crate allows you to initialize arrays
//! with an initializer closure that will be called
//! once for each element until the array is filled.
//!
//! This way you do not need to default-fill an array
//! before running initializers. Rust currently only
//! lets you either specify all initializers at once,
//! individually (`[a(), b(), c(), ...]`), or specify
//! one initializer for a `Copy` type (`[a(); N]`),
//! which will be called once with the result copied over.
//!
//! # Examples:
//! ```rust
//! # #![allow(unused)]
//! # extern crate array_init;
//! #
//! // Initialize an array of length 50 containing
//! // successive squares
//!
//! let arr: [u32; 50] = array_init::array_init(|i: usize| (i * i) as u32);
//!
//! // Initialize an array from an iterator
//! // producing an array of [1,2,3,4] repeated
//!
//! let four = [1,2,3,4];
//! let mut iter = four.iter().copied().cycle();
//! let arr: [u32; 50] = array_init::from_iter(iter).unwrap();
//!
//! // Closures can also mutate state. We guarantee that they will be called
//! // in order from lower to higher indices.
//!
//! let mut last = 1u64;
//! let mut secondlast = 0;
//! let fibonacci: [u64; 50] = array_init::array_init(|_| {
//!     let this = last + secondlast;
//!     secondlast = last;
//!     last = this;
//!     this
//! });
//! ```

use ::core::{
    mem::{self,
        MaybeUninit,
    },
    ptr,
    slice,
};

/// Trait for things which are actually arrays.
///
/// Probably shouldn't implement this yourself, but you can.
///
/// # Safety
///
///   - if `Array : IsArray`, then it must be sound to transmute
///     between `Array` and `[Array::Item; Array::len()]`
pub unsafe trait IsArray {
    /// The stored `T`
    type Item;

    /// The number of elements of the array
    fn len() -> usize;
}

#[inline]
/// Initialize an array given an initializer expression.
///
/// The initializer is given the index of the element. It is allowed
/// to mutate external state; we will always initialize the elements in order.
///
/// # Examples
///
/// ```rust
/// # #![allow(unused)]
/// # extern crate array_init;
/// #
/// // Initialize an array of length 50 containing
/// // successive squares
/// let arr: [usize; 50] = array_init::array_init(|i| i * i);
///
/// assert!(arr.iter().enumerate().all(|(i, &x)| x == i * i));
/// ```
pub fn array_init<Array, F> (
    mut initializer: F,
) -> Array
where
    Array : IsArray,
    F : FnMut(usize) -> Array::Item,
{
    enum Unreachable {}

    try_array_init( // monomorphise into an unfallible version
        move |i| -> Result<Array::Item, Unreachable> {
            Ok(initializer(i))
        }
    ).unwrap_or_else( // zero-cost unwrap
        |unreachable| match unreachable { /* ! */ }
    )
}

#[inline]
/// Initialize an array given an iterator
///
/// We will iterate until the array is full or the iterator is exhausted. Returns
/// `None` if the iterator is exhausted before we can fill the array.
///
///   - Once the array is full, extra elements from the iterator (if any)
///     won't be consumed.
///
/// # Examples
///
/// ```rust
/// # #![allow(unused)]
/// # extern crate array_init;
/// #
/// // Initialize an array from an iterator
/// // producing an array of [1,2,3,4] repeated
///
/// let four = [1,2,3,4];
/// let mut iter = four.iter().copied().cycle();
/// let arr: [u32; 50] = array_init::from_iter(iter).unwrap();
/// ```
pub fn from_iter<Array, Iterable> (
    iterable: Iterable,
) -> Option<Array>
where
    Iterable : IntoIterator<Item = Array::Item>,
    Array : IsArray,
{
    try_array_init({
        let mut iterator = iterable.into_iter();
        move |_| {
            iterator.next().ok_or(())
        }
    }).ok()
}

#[inline]
pub fn try_array_init<Array, Err, F> (
    mut initializer: F,
) -> Result<Array, Err>
where
    Array : IsArray,
    F : FnMut(usize) -> Result<Array::Item, Err>,
{
    if !mem::needs_drop::<Array::Item>() {
        let mut array: MaybeUninit<Array> = MaybeUninit::uninit();
        // pointer to array = *mut [T; N] <-> *mut T = pointer to first element
        let mut ptr_i = array.as_mut_ptr() as *mut Array::Item;

        //   - Using `ptr::add` instead of `offset` avoids having to check
        //     that the offset in bytes does not overflow isize.
        //
        // # Safety
        //
        //   - `IsArray`'s contract guarantees that we are within the array
        //     since we have `0 <= i < Array::len`
        unsafe {
            for i in 0 .. Array::len() {
                let value_i = initializer(i)?;
                ptr_i.write(value_i);
                ptr_i = ptr_i.add(1);
            }
            return Ok(array.assume_init());
        }
    }

    // else: `mem::needs_drop::<Array::Item>()`

    /// # Safety
    ///
    ///   - `base_ptr[.. initialized_count]` must be a slice of init elements...
    ///
    ///   - ... that must be sound to `ptr::drop_in_place` if/when
    ///     `UnsafeDropSliceGuard` is dropped: "symbolic ownership"
    struct UnsafeDropSliceGuard<Item> {
        base_ptr: *mut Item,
        initialized_count: usize,
    }

    impl<Item> Drop for UnsafeDropSliceGuard<Item> {
        fn drop (self: &'_ mut Self)
        {
            unsafe {
                // # Safety
                //
                //   - the contract of the struct guarantees that this is sound
                ptr::drop_in_place(
                    slice::from_raw_parts_mut(
                        self.base_ptr,
                        self.initialized_count,
                    )
                );
            }
        }
    }

    //  1. If the `initializer(i)` call panics, `panic_guard` is dropped,
    //     dropping `array[.. initialized_count]` => no memory leak!
    //
    //  2. Using `ptr::add` instead of `offset` avoids having to check
    //     that the offset in bytes does not overflow isize.
    //
    // # Safety
    //
    //  1. By construction, array[.. initiliazed_count] only contains
    //     init elements, thus there is no risk of dropping uninit data;
    //
    //  2. `IsArray`'s contract guarantees that we are within the array
    //     since we have `0 <= i < Array::len`
    unsafe {
        let mut array: MaybeUninit<Array> = MaybeUninit::uninit();
        // pointer to array = *mut [T; N] <-> *mut T = pointer to first element
        let mut ptr_i = array.as_mut_ptr() as *mut Array::Item;
        let mut panic_guard = UnsafeDropSliceGuard {
            base_ptr: ptr_i,
            initialized_count: 0,
        };

        for i in 0 .. Array::len() {
            // Invariant: `i` elements have already been initialized
            panic_guard.initialized_count = i;
            // If this panics or fails, `panic_guard` is dropped, thus
            // dropping the elements in `base_ptr[.. i]`
            let value_i = initializer(i)?;
            // this cannot panic
            ptr_i.write(value_i);
            ptr_i = ptr_i.add(1);
        }
        // From now on, the code can no longer `panic!`, let's take the
        // symbolic ownership back
        mem::forget(panic_guard);

        Ok(array.assume_init())
    }
}

unsafe impl<T, const N: usize> IsArray for [T; N] {
    type Item = T;

    #[inline]
    fn len() -> usize {
        N
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seq ()
    {
        let seq: [usize; 5] = array_init(|i| i);
        assert_eq!(&[0, 1, 2, 3, 4], &seq);
    }

    #[test]
    fn array_from_iter ()
    {
        let array = [0, 1, 2, 3, 4];
        let seq: [usize; 5] = from_iter(array.iter().copied()).unwrap();
        assert_eq!(
            array,
            seq,
        );
    }

    #[test]
    fn array_init_no_drop ()
    {
        DropChecker::with(|drop_checker| {
            let result: Result<[_; 5], ()> =
                try_array_init(|i| {
                    if i < 3 {
                        Ok(drop_checker.new_element())
                    } else {
                        Err(())
                    }
                })
            ;
            assert!(result.is_err());
        });
    }

    #[test]
    fn from_iter_no_drop ()
    {
        DropChecker::with(|drop_checker| {
            let iterator = (0 .. 3).map(|_| drop_checker.new_element());
            let result: Option<[_; 5]> = from_iter(iterator);
            assert!(result.is_none());
        });
    }

    use self::drop_checker::DropChecker;
    mod drop_checker {
        use ::core::cell::Cell;

        pub(in super)
        struct DropChecker {
            slots: [Cell<bool>; 512],
            next_uninit_slot: Cell<usize>,
        }

        pub(in super)
        struct Element<'drop_checker> {
            slot: &'drop_checker Cell<bool>,
        }

        impl Drop for Element<'_> {
            fn drop (self: &'_ mut Self)
            {
                assert!(self.slot.replace(false), "Double free!");
            }
        }

        impl DropChecker {
            pub(in super)
            fn with (f: impl FnOnce(&Self))
            {
                let drop_checker = Self::new();
                f(&drop_checker);
                drop_checker.assert_no_leaks();
            }

            pub(in super)
            fn new_element (self: &'_ Self) -> Element<'_>
            {
                let i = self.next_uninit_slot.get();
                self.next_uninit_slot.set(i + 1);
                self.slots[i].set(true);
                Element {
                    slot: &self.slots[i],
                }
            }

            fn new () -> Self
            {
                Self {
                    slots: crate::array_init(|_| Cell::new(false)),
                    next_uninit_slot: Cell::new(0),
                }
            }

            fn assert_no_leaks (self: Self)
            {
                let leak_count: usize =
                    self.slots[.. self.next_uninit_slot.get()]
                        .iter()
                        .map(|slot| usize::from(slot.get() as u8))
                        .sum()
                ;
                assert_eq!(leak_count, 0, "No elements leaked");
            }
        }
    }
}
