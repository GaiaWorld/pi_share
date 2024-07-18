use std::{ops::{Deref, DerefMut}, ptr::NonNull, rc::Rc};




pub struct Xrc<T: ?Sized>(Rc<T>);

impl<T: ?Sized> Clone for Xrc<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized> Deref for Xrc<T> {
    type Target = Rc<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T: ?Sized> DerefMut for Xrc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> Xrc<T> {
    pub fn new(val: T) -> Self {
        Self(Rc::new(val))
    }

    // /// Constructs a new `Rc<T>` while giving you a `Weak<T>` to the allocation,
    // /// to allow you to construct a `T` which holds a weak pointer to itself.
    // ///
    // /// Generally, a structure circularly referencing itself, either directly or
    // /// indirectly, should not hold a strong reference to itself to prevent a memory leak.
    // /// Using this function, you get access to the weak pointer during the
    // /// initialization of `T`, before the `Rc<T>` is created, such that you can
    // /// clone and store it inside the `T`.
    // ///
    // /// `new_cyclic` first allocates the managed allocation for the `Rc<T>`,
    // /// then calls your closure, giving it a `Weak<T>` to this allocation,
    // /// and only afterwards completes the construction of the `Rc<T>` by placing
    // /// the `T` returned from your closure into the allocation.
    // ///
    // /// Since the new `Rc<T>` is not fully-constructed until `Rc<T>::new_cyclic`
    // /// returns, calling [`upgrade`] on the weak reference inside your closure will
    // /// fail and result in a `None` value.
    // ///
    // /// # Panics
    // ///
    // /// If `data_fn` panics, the panic is propagated to the caller, and the
    // /// temporary [`Weak<T>`] is dropped normally.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// # #![allow(dead_code)]
    // /// use std::rc::{Rc, Weak};
    // ///
    // /// struct Gadget {
    // ///     me: Weak<Gadget>,
    // /// }
    // ///
    // /// impl Gadget {
    // ///     /// Construct a reference counted Gadget.
    // ///     fn new() -> Rc<Self> {
    // ///         // `me` is a `Weak<Gadget>` pointing at the new allocation of the
    // ///         // `Rc` we're constructing.
    // ///         Rc::new_cyclic(|me| {
    // ///             // Create the actual struct here.
    // ///             Gadget { me: me.clone() }
    // ///         })
    // ///     }
    // ///
    // ///     /// Return a reference counted pointer to Self.
    // ///     fn me(&self) -> Rc<Self> {
    // ///         self.me.upgrade().unwrap()
    // ///     }
    // /// }
    // /// ```
    // /// [`upgrade`]: Weak::upgrade
    // #[cfg(not(no_global_oom_handling))]
    // #[stable(feature = "arc_new_cyclic", since = "1.60.0")]
    // pub fn new_cyclic<F>(data_fn: F) -> Rc<T>
    // where
    //     F: FnOnce(&Weak<T>) -> T,
    // {
    //     // Construct the inner in the "uninitialized" state with a single
    //     // weak reference.
    //     let uninit_ptr: NonNull<_> = Box::leak(Box::new(RcBox {
    //         strong: Cell::new(0),
    //         weak: Cell::new(1),
    //         value: mem::MaybeUninit::<T>::uninit(),
    //     }))
    //     .into();

    //     let init_ptr: NonNull<RcBox<T>> = uninit_ptr.cast();

    //     let weak = Weak { ptr: init_ptr };

    //     // It's important we don't give up ownership of the weak pointer, or
    //     // else the memory might be freed by the time `data_fn` returns. If
    //     // we really wanted to pass ownership, we could create an additional
    //     // weak pointer for ourselves, but this would result in additional
    //     // updates to the weak reference count which might not be necessary
    //     // otherwise.
    //     let data = data_fn(&weak);

    //     let strong = unsafe {
    //         let inner = init_ptr.as_ptr();
    //         ptr::write(ptr::addr_of_mut!((*inner).value), data);

    //         let prev_value = (*inner).strong.get();
    //         debug_assert_eq!(prev_value, 0, "No prior strong references should exist");
    //         (*inner).strong.set(1);

    //         Rc::from_inner(init_ptr)
    //     };

    //     // Strong references should collectively own a shared weak reference,
    //     // so don't run the destructor for our old weak reference.
    //     mem::forget(weak);
    //     strong
    // }

    // /// Constructs a new `Rc` with uninitialized contents.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(new_uninit)]
    // /// #![feature(get_mut_unchecked)]
    // ///
    // /// use std::rc::Rc;
    // ///
    // /// let mut five = Rc::<u32>::new_uninit();
    // ///
    // /// // Deferred initialization:
    // /// Rc::get_mut(&mut five).unwrap().write(5);
    // ///
    // /// let five = unsafe { five.assume_init() };
    // ///
    // /// assert_eq!(*five, 5)
    // /// ```
    // #[cfg(not(no_global_oom_handling))]
    // #[unstable(feature = "new_uninit", issue = "63291")]
    // #[must_use]
    // pub fn new_uninit() -> Rc<mem::MaybeUninit<T>> {
    //     unsafe {
    //         Rc::from_ptr(Rc::allocate_for_layout(
    //             Layout::new::<T>(),
    //             |layout| Global.allocate(layout),
    //             |mem| mem as *mut RcBox<mem::MaybeUninit<T>>,
    //         ))
    //     }
    // }

    // /// Constructs a new `Rc` with uninitialized contents, with the memory
    // /// being filled with `0` bytes.
    // ///
    // /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and
    // /// incorrect usage of this method.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(new_uninit)]
    // ///
    // /// use std::rc::Rc;
    // ///
    // /// let zero = Rc::<u32>::new_zeroed();
    // /// let zero = unsafe { zero.assume_init() };
    // ///
    // /// assert_eq!(*zero, 0)
    // /// ```
    // ///
    // /// [zeroed]: mem::MaybeUninit::zeroed
    // #[cfg(not(no_global_oom_handling))]
    // #[unstable(feature = "new_uninit", issue = "63291")]
    // #[must_use]
    // pub fn new_zeroed() -> Rc<mem::MaybeUninit<T>> {
    //     unsafe {
    //         Rc::from_ptr(Rc::allocate_for_layout(
    //             Layout::new::<T>(),
    //             |layout| Global.allocate_zeroed(layout),
    //             |mem| mem as *mut RcBox<mem::MaybeUninit<T>>,
    //         ))
    //     }
    // }

    // /// Constructs a new `Rc<T>`, returning an error if the allocation fails
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(allocator_api)]
    // /// use std::rc::Rc;
    // ///
    // /// let five = Rc::try_new(5);
    // /// # Ok::<(), std::alloc::AllocError>(())
    // /// ```
    // #[unstable(feature = "allocator_api", issue = "32838")]
    // pub fn try_new(value: T) -> Result<Rc<T>, AllocError> {
    //     // There is an implicit weak pointer owned by all the strong
    //     // pointers, which ensures that the weak destructor never frees
    //     // the allocation while the strong destructor is running, even
    //     // if the weak pointer is stored inside the strong one.
    //     unsafe {
    //         Ok(Self::from_inner(
    //             Box::leak(Box::try_new(RcBox { strong: Cell::new(1), weak: Cell::new(1), value })?)
    //                 .into(),
    //         ))
    //     }
    // }

    // /// Constructs a new `Rc` with uninitialized contents, returning an error if the allocation fails
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(allocator_api, new_uninit)]
    // /// #![feature(get_mut_unchecked)]
    // ///
    // /// use std::rc::Rc;
    // ///
    // /// let mut five = Rc::<u32>::try_new_uninit()?;
    // ///
    // /// // Deferred initialization:
    // /// Rc::get_mut(&mut five).unwrap().write(5);
    // ///
    // /// let five = unsafe { five.assume_init() };
    // ///
    // /// assert_eq!(*five, 5);
    // /// # Ok::<(), std::alloc::AllocError>(())
    // /// ```
    // #[unstable(feature = "allocator_api", issue = "32838")]
    // // #[unstable(feature = "new_uninit", issue = "63291")]
    // pub fn try_new_uninit() -> Result<Rc<mem::MaybeUninit<T>>, AllocError> {
    //     unsafe {
    //         Ok(Rc::from_ptr(Rc::try_allocate_for_layout(
    //             Layout::new::<T>(),
    //             |layout| Global.allocate(layout),
    //             |mem| mem as *mut RcBox<mem::MaybeUninit<T>>,
    //         )?))
    //     }
    // }

    // /// Constructs a new `Rc` with uninitialized contents, with the memory
    // /// being filled with `0` bytes, returning an error if the allocation fails
    // ///
    // /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and
    // /// incorrect usage of this method.
    // ///
    // /// # Examples
    // ///
    // /// ```
    // /// #![feature(allocator_api, new_uninit)]
    // ///
    // /// use std::rc::Rc;
    // ///
    // /// let zero = Rc::<u32>::try_new_zeroed()?;
    // /// let zero = unsafe { zero.assume_init() };
    // ///
    // /// assert_eq!(*zero, 0);
    // /// # Ok::<(), std::alloc::AllocError>(())
    // /// ```
    // ///
    // /// [zeroed]: mem::MaybeUninit::zeroed
    // #[unstable(feature = "allocator_api", issue = "32838")]
    // //#[unstable(feature = "new_uninit", issue = "63291")]
    // pub fn try_new_zeroed() -> Result<Rc<mem::MaybeUninit<T>>, AllocError> {
    //     unsafe {
    //         Ok(Rc::from_ptr(Rc::try_allocate_for_layout(
    //             Layout::new::<T>(),
    //             |layout| Global.allocate_zeroed(layout),
    //             |mem| mem as *mut RcBox<mem::MaybeUninit<T>>,
    //         )?))
    //     }
    // }
    // /// Constructs a new `Pin<Rc<T>>`. If `T` does not implement `Unpin`, then
    // /// `value` will be pinned in memory and unable to be moved.
    // #[cfg(not(no_global_oom_handling))]
    // #[stable(feature = "pin", since = "1.33.0")]
    // #[must_use]
    // pub fn pin(value: T) -> Pin<Rc<T>> {
    //     unsafe { Pin::new_unchecked(Rc::new(value)) }
    // }
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        match Rc::try_unwrap(this.0) {
            Ok(r) => Ok(r),
            Err(r) => Err(Self(r)),
        }
    }
}

unsafe impl<T: ?Sized + Send> Send for Xrc<T> {}
unsafe impl<T: ?Sized + Sync> Sync for Xrc<T> {}



