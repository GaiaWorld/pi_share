//! Helper module for some internals, most users don't need to interact with it.

use std::{
    cell::UnsafeCell,
    error::Error,
    fmt::{Display, Error as FormatError, Formatter},
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering},
    usize,
};

/// Marker struct for an invalid borrow error
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct InvalidBorrow;

impl Display for InvalidBorrow {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FormatError> {
        write!(f, "Tried to borrow when it was illegal")
    }
}

impl Error for InvalidBorrow {
    fn description(&self) -> &str {
        "This error is returned when you try to borrow immutably when it's already \
         borrowed mutably or you try to borrow mutably when it's already borrowed"
    }
}

/// An immutable reference to data in a `TrustCell`.
///
/// Access the value via `std::ops::Deref` (e.g. `*val`)
#[derive(Debug)]
pub struct Ref<'a, T: 'a + ?Sized> {
    flag: &'a AtomicUsize,
    value: &'a T,
}

impl<'a, T: ?Sized> Deref for Ref<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<'a, T: ?Sized> Drop for Ref<'a, T> {
    fn drop(&mut self) {
        self.flag.fetch_sub(1, Ordering::Release);
    }
}

impl<'a, T: ?Sized> Ref<'a, T> {
    /// Makes a new `Ref` for a component of the borrowed data which preserves
    /// the existing borrow.
    ///
    /// The `TrustCell` is already immutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as `Ref::map(...)`.
    /// A method would interfere with methods of the same name on the contents
    /// of a `Ref` used through `Deref`. Further this preserves the borrow of
    /// the value and hence does the proper cleanup when it's dropped.
    ///
    /// # Examples
    ///
    /// This can be used to avoid pointer indirection when a boxed item is
    /// stored in the `TrustCell`.
    ///
    /// ```
    /// use shred::cell::{Ref, TrustCell};
    ///
    /// let cb = TrustCell::new(Box::new(5));
    ///
    /// // Borrowing the cell causes the `Ref` to store a reference to the `Box`, which is a
    /// // pointer to the value on the heap, not the actual value.
    /// let boxed_ref: Ref<'_, Box<usize>> = cb.borrow();
    /// assert_eq!(**boxed_ref, 5); // Notice the double deref to get the actual value.
    ///
    /// // By using `map` we can let `Ref` store a reference directly to the value on the heap.
    /// let pure_ref: Ref<'_, usize> = Ref::map(boxed_ref, Box::as_ref);
    ///
    /// assert_eq!(*pure_ref, 5);
    /// ```
    ///
    /// We can also use `map` to get a reference to a sub-part of the borrowed
    /// value.
    ///
    /// ```rust
    /// # use shred::cell::{TrustCell, Ref};
    ///
    /// let c = TrustCell::new((5, 'b'));
    /// let b1: Ref<'_, (u32, char)> = c.borrow();
    /// let b2: Ref<'_, u32> = Ref::map(b1, |t| &t.0);
    /// assert_eq!(*b2, 5);
    /// ```
    pub fn map<U, F>(self, f: F) -> Ref<'a, U>
    where
        F: FnOnce(&T) -> &U,
        U: ?Sized,
    {
        let val = Ref {
            flag: self.flag,
            value: f(self.value),
        };

        std::mem::forget(self);

        val
    }
}

/// A mutable reference to data in a `TrustCell`.
///
/// Access the value via `std::ops::DerefMut` (e.g. `*val`)
#[derive(Debug)]
pub struct RefMut<'a, T: 'a + ?Sized> {
    flag: &'a AtomicUsize,
    value: &'a mut T,
}

impl<'a, T: ?Sized> Deref for RefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.value
    }
}

impl<'a, T: ?Sized> DerefMut for RefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        self.value
    }
}

impl<'a, T: ?Sized> Drop for RefMut<'a, T> {
    fn drop(&mut self) {
        self.flag.store(0, Ordering::Release)
    }
}

impl<'a, T: ?Sized> RefMut<'a, T> {
    /// Makes a new `RefMut` for a component of the borrowed data which
    /// preserves the existing borrow.
    ///
    /// The `TrustCell` is already mutably borrowed, so this cannot fail.
    ///
    /// This is an associated function that needs to be used as
    /// `RefMut::map(...)`. A method would interfere with methods of the
    /// same name on the contents of a `RefMut` used through `DerefMut`.
    /// Further this preserves the borrow of the value and hence does the
    /// proper cleanup when it's dropped.
    ///
    /// # Examples
    ///
    /// This can also be used to avoid pointer indirection when a boxed item is
    /// stored in the `TrustCell`.
    ///
    /// ```
    /// use shred::cell::{RefMut, TrustCell};
    ///
    /// let cb = TrustCell::new(Box::new(5));
    ///
    /// // Borrowing the cell causes the `RefMut` to store a reference to the `Box`, which is a
    /// // pointer to the value on the heap, and not a reference directly to the value.
    /// let boxed_ref: RefMut<'_, Box<usize>> = cb.borrow_mut();
    /// assert_eq!(**boxed_ref, 5); // Notice the double deref to get the actual value.
    ///
    /// // By using `map` we can let `RefMut` store a reference directly to the value on the heap.
    /// let pure_ref: RefMut<'_, usize> = RefMut::map(boxed_ref, Box::as_mut);
    ///
    /// assert_eq!(*pure_ref, 5);
    /// ```
    ///
    /// We can also use `map` to get a reference to a sub-part of the borrowed
    /// value.
    ///
    /// ```rust
    /// # use shred::cell::{TrustCell, RefMut};
    ///
    /// let c = TrustCell::new((5, 'b'));
    ///
    /// let b1: RefMut<'_, (u32, char)> = c.borrow_mut();
    /// let b2: RefMut<'_, u32> = RefMut::map(b1, |t| &mut t.0);
    /// assert_eq!(*b2, 5);
    /// ```
    pub fn map<U, F>(self, f: F) -> RefMut<'a, U>
    where
        F: FnOnce(&mut T) -> &mut U,
        U: ?Sized,
    {
        // Extract the values from the `RefMut` through a pointer so that we do not run
        // `Drop`. Because the returned `RefMut` has the same lifetime `'a` as
        // the given `RefMut`, the lifetime we created through turning the
        // pointer into a ref is valid.
        let flag = self.flag;
        let value = unsafe { &mut *(self.value as *mut _) };

        // We have to forget self so that we do not run `Drop`. Further it's safe
        // because we are creating a new `RefMut`, with the same flag, which
        // will run the cleanup when it's dropped.
        std::mem::forget(self);

        RefMut {
            flag,
            value: f(value),
        }
    }
}

/// A custom cell container that is a `RefCell` with thread-safety.
#[derive(Debug)]
pub struct TrustCell<T: ?Sized> {
    flag: AtomicUsize,
    inner: UnsafeCell<T>,
}
unsafe impl<T: ?Sized> Sync for TrustCell<T> where T: Sync {}
unsafe impl<T: ?Sized> Send for TrustCell<T> where T: Send {}

impl<T> TrustCell<T> {
    /// Create a new cell, similar to `RefCell::new`
    pub fn new(val: T) -> Self {
        TrustCell {
            flag: AtomicUsize::new(0),
            inner: UnsafeCell::new(val),
        }
    }
    /// Consumes this cell and returns ownership of `T`.
    pub fn into_inner(self) -> T {
        self.inner.into_inner()
    }
}

impl<T: ?Sized> TrustCell<T> {
    pub fn as_ptr(&self) -> *mut T {
        self.inner.get()
    }

    /// Get an immutable reference to the inner data.
    ///
    /// Absence of write accesses is checked at run-time.
    ///
    /// # Panics
    ///
    /// This function will panic if there is a mutable reference to the data
    /// already in use.
    pub fn borrow(&self) -> Ref<T> {
        self.check_flag_read().expect("Already borrowed mutably");

        Ref {
            flag: &self.flag,
            value: unsafe { &*self.inner.get() },
        }
    }

    /// Get an immutable reference to the inner data.
    ///
    /// Absence of write accesses is checked at run-time. If access is not
    /// possible, an error is returned.
    pub fn try_borrow(&self) -> Result<Ref<T>, InvalidBorrow> {
        self.check_flag_read()?;

        Ok(Ref {
            flag: &self.flag,
            value: unsafe { &*self.inner.get() },
        })
    }

    /// Get a mutable reference to the inner data.
    ///
    /// Exclusive access is checked at run-time.
    ///
    /// # Panics
    ///
    /// This function will panic if there are any references to the data already
    /// in use.
    pub fn borrow_mut(&self) -> RefMut<T> {
        self.check_flag_write().expect("Already borrowed");

        RefMut {
            flag: &self.flag,
            value: unsafe { &mut *self.inner.get() },
        }
    }

    /// Get a mutable reference to the inner data.
    ///
    /// Exclusive access is checked at run-time. If access is not possible, an
    /// error is returned.
    pub fn try_borrow_mut(&self) -> Result<RefMut<T>, InvalidBorrow> {
        self.check_flag_write()?;

        Ok(RefMut {
            flag: &self.flag,
            value: unsafe { &mut *self.inner.get() },
        })
    }

    /// Gets exclusive access to the inner value, bypassing the Cell.
    ///
    /// Exclusive access is checked at compile time.
    pub fn get_mut(&mut self) -> &mut T {
        // safe because we have exclusive access via &mut self
        unsafe { &mut *self.inner.get() }
    }

    pub fn get(&self) -> &T {
        // safe because we have exclusive access via &mut self
        unsafe { &*self.inner.get() }
    }

    /// Make sure we are allowed to aquire a read lock, and increment the read
    /// count by 1
    fn check_flag_read(&self) -> Result<(), InvalidBorrow> {
        // Check that no write reference is out, then try to increment the read count
        // and return once successful.
        loop {
            let val = self.flag.load(Ordering::Acquire);

            if val == usize::MAX {
                return Err(InvalidBorrow);
            }

            match self
                .flag
                .compare_exchange(val, val + 1, Ordering::AcqRel, Ordering::Relaxed)
            {
                Ok(r) => {
                    if r == val {
                        return Ok(());
                    }
                }
                _ => continue,
            }
        }
    }

    /// Make sure we are allowed to aquire a write lock, and then set the write
    /// lock flag.
    fn check_flag_write(&self) -> Result<(), InvalidBorrow> {
        // Check we have 0 references out, and then set the ref count to usize::MAX to
        // indicate a write lock.
        match self
            .flag
            .compare_exchange(0, usize::MAX, Ordering::AcqRel, Ordering::Relaxed)
        {
            Ok(_r) => Ok(()),
            _ => Err(InvalidBorrow),
        }
    }
}

impl<T: Default> Default for TrustCell<T> {
    fn default() -> Self {
        TrustCell::new(Default::default())
    }
}
// impl<T> const From<T> for TrustCell<T> {
//     fn from(t: T) -> Self {
//         TrustCell::new(t)
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn allow_multiple_reads() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let a = cell.borrow();
        let b = cell.borrow();

        assert_eq!(10, *a + *b);
    }

    #[test]
    fn allow_single_write() {
        let cell: TrustCell<_> = TrustCell::new(5);

        {
            let mut a = cell.borrow_mut();
            *a += 2;
            *a += 3;
        }

        assert_eq!(10, *cell.borrow());
    }

    #[test]
    #[should_panic(expected = "Already borrowed mutably")]
    fn panic_write_and_read() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let mut a = cell.borrow_mut();
        *a = 7;

        assert_eq!(7, *cell.borrow());
    }

    #[test]
    #[should_panic(expected = "Already borrowed")]
    fn panic_write_and_write() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let mut a = cell.borrow_mut();
        *a = 7;

        assert_eq!(7, *cell.borrow_mut());
    }

    #[test]
    #[should_panic(expected = "Already borrowed")]
    fn panic_read_and_write() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let _a = cell.borrow();

        assert_eq!(7, *cell.borrow_mut());
    }

    #[test]
    fn try_write_and_read() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let mut a = cell.try_borrow_mut().unwrap();
        *a = 7;

        assert!(cell.try_borrow().is_err());
    }

    #[test]
    fn try_write_and_write() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let mut a = cell.try_borrow_mut().unwrap();
        *a = 7;

        assert!(cell.try_borrow_mut().is_err());
    }

    #[test]
    fn try_read_and_write() {
        let cell: TrustCell<_> = TrustCell::new(5);

        let _a = cell.try_borrow().unwrap();

        assert!(cell.try_borrow_mut().is_err());
    }
}
