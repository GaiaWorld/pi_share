//! Thread-safe reference-counting pointers.
//!
//! See the [`Xrc<T>`][Xrc] documentation for more details.
//!
//! **Note**: This module is only available on platforms that support atomic
//! loads and stores of pointers. This may be detected at compile time using
//! `#[cfg(target_has_atomic = "ptr")]`.

use crate::ShareUsize;

use core::any::Any;
use core::borrow;
use core::cmp::Ordering;
use core::fmt;
use core::hash::{Hash, Hasher};
use core::hint;
#[cfg(not(no_global_oom_handling))]
use core::iter;
use core::marker::PhantomData;
#[cfg(not(no_global_oom_handling))]
use core::ops::Deref;
use core::panic::{RefUnwindSafe, UnwindSafe};
use core::pin::Pin;
use core::ptr::{self, NonNull};
#[cfg(not(no_global_oom_handling))]
use core::slice::from_raw_parts_mut;
use core::sync::atomic::Ordering::{Acquire, Relaxed, Release};

#[cfg(not(no_global_oom_handling))]
use std::alloc::handle_alloc_error;
#[cfg(not(no_global_oom_handling))]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::borrow::{Cow, ToOwned};
use std::boxed::Box;
use std::intrinsics::{abort, min_align_of_val};
use std::mem::{align_of_val_raw, forget, size_of_val, ManuallyDrop, MaybeUninit};
use std::ops::Receiver;
use std::ptr::Unique;
#[cfg(not(no_global_oom_handling))]
use std::string::String;
#[cfg(not(no_global_oom_handling))]
use std::vec::Vec;

/// A soft limit on the amount of references that may be made to an `Xrc`.
///
/// Going above this limit will abort your program (although not
/// necessarily) at _exactly_ `MAX_REFCOUNT + 1` references.
/// Trying to go above it might call a `panic` (if not actually going above it).
///
/// This is a global invariant, and also applies when using a compare-exchange loop.
///
/// See comment in `Xrc::clone`.
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

/// The error in case either counter reaches above `MAX_REFCOUNT`, and we can `panic` safely.
const INTERNAL_OVERFLOW_ERROR: &str = "Xrc counter overflow";

/// A thread-safe reference-counting pointer. 'Xrc' stands for 'Atomically
/// Reference Counted'.
///
/// The type `Xrc<T>` provides shared ownership of a value of type `T`,
/// allocated in the heap. Invoking [`clone`][clone] on `Xrc` produces
/// a new `Xrc` instance, which points to the same allocation on the heap as the
/// source `Xrc`, while increasing a reference count. When the last `Xrc`
/// pointer to a given allocation is destroyed, the value stored in that allocation (often
/// referred to as "inner value") is also dropped.
///
/// Shared references in Rust disallow mutation by default, and `Xrc` is no
/// exception: you cannot generally obtain a mutable reference to something
/// inside an `Xrc`. If you need to mutate through an `Xrc`, use
/// [`Mutex`][mutex], [`RwLock`][rwlock], or one of the [`Atomic`][atomic]
/// types.
///
/// **Note**: This type is only available on platforms that support atomic
/// loads and stores of pointers, which includes all platforms that support
/// the `std` crate but not all those which only support [`alloc`](crate).
/// This may be detected at compile time using `#[cfg(target_has_atomic = "ptr")]`.
///
/// ## Thread Safety
///
/// Unlike [`Rc<T>`], `Xrc<T>` uses atomic operations for its reference
/// counting. This means that it is thread-safe. The disadvantage is that
/// atomic operations are more expensive than ordinary memory accesses. If you
/// are not sharing reference-counted allocations between threads, consider using
/// [`Rc<T>`] for lower overhead. [`Rc<T>`] is a safe default, because the
/// compiler will catch any attempt to send an [`Rc<T>`] between threads.
/// However, a library might choose `Xrc<T>` in order to give library consumers
/// more flexibility.
///
/// `Xrc<T>` will implement [`Send`] and [`Sync`] as long as the `T` implements
/// [`Send`] and [`Sync`]. Why can't you put a non-thread-safe type `T` in an
/// `Xrc<T>` to make it thread-safe? This may be a bit counter-intuitive at
/// first: after all, isn't the point of `Xrc<T>` thread safety? The key is
/// this: `Xrc<T>` makes it thread safe to have multiple ownership of the same
/// data, but it  doesn't add thread safety to its data. Consider
/// <code>Xrc<[RefCell\<T>]></code>. [`RefCell<T>`] isn't [`Sync`], and if `Xrc<T>` was always
/// [`Send`], <code>Xrc<[RefCell\<T>]></code> would be as well. But then we'd have a problem:
/// [`RefCell<T>`] is not thread safe; it keeps track of the borrowing count using
/// non-atomic operations.
///
/// In the end, this means that you may need to pair `Xrc<T>` with some sort of
/// [`std::sync`] type, usually [`Mutex<T>`][mutex].
///
/// ## Breaking cycles with `Weak`
///
/// The [`downgrade`][downgrade] method can be used to create a non-owning
/// [`Weak`] pointer. A [`Weak`] pointer can be [`upgrade`][upgrade]d
/// to an `Xrc`, but this will return [`None`] if the value stored in the allocation has
/// already been dropped. In other words, `Weak` pointers do not keep the value
/// inside the allocation alive; however, they *do* keep the allocation
/// (the backing store for the value) alive.
///
/// A cycle between `Xrc` pointers will never be deallocated. For this reason,
/// [`Weak`] is used to break cycles. For example, a tree could have
/// strong `Xrc` pointers from parent nodes to children, and [`Weak`]
/// pointers from children back to their parents.
///
/// # Cloning references
///
/// Creating a new reference from an existing reference-counted pointer is done using the
/// `Clone` trait implemented for [`Xrc<T>`][Xrc] and [`Weak<T>`][Weak].
///
/// ```
/// use pi_share::xrc::Xrc;
/// let foo = Xrc::new(vec![1.0, 2.0, 3.0]);
/// // The two syntaxes below are equivalent.
/// let a = foo.clone();
/// let b = Xrc::clone(&foo);
/// // a, b, and foo are all Xrcs that point to the same memory location
/// ```
///
/// ## `Deref` behavior
///
/// `Xrc<T>` automatically dereferences to `T` (via the [`Deref`][deref] trait),
/// so you can call `T`'s methods on a value of type `Xrc<T>`. To avoid name
/// clashes with `T`'s methods, the methods of `Xrc<T>` itself are associated
/// functions, called using [fully qualified syntax]:
///
/// ```
/// use pi_share::xrc::Xrc;
///
/// let my_Xrc = Xrc::new(());
/// let my_weak = Xrc::downgrade(&my_Xrc);
/// ```
///
/// `Xrc<T>`'s implementations of traits like `Clone` may also be called using
/// fully qualified syntax. Some people prefer to use fully qualified syntax,
/// while others prefer using method-call syntax.
///
/// ```
/// use pi_share::xrc::Xrc;
///
/// let Xrc = Xrc::new(());
/// // Method-call syntax
/// let Xrc2 = Xrc.clone();
/// // Fully qualified syntax
/// let Xrc3 = Xrc::clone(&Xrc);
/// ```
///
/// [`Weak<T>`][Weak] does not auto-dereference to `T`, because the inner value may have
/// already been dropped.
///
/// [`Rc<T>`]: crate::rc::Rc
/// [clone]: Clone::clone
/// [mutex]: ../../std/sync/struct.Mutex.html
/// [rwlock]: ../../std/sync/struct.RwLock.html
/// [atomic]: core::sync::atomic
/// [deref]: core::ops::Deref
/// [downgrade]: Xrc::downgrade
/// [upgrade]: Weak::upgrade
/// [RefCell\<T>]: core::cell::RefCell
/// [`RefCell<T>`]: core::cell::RefCell
/// [`std::sync`]: ../../std/sync/index.html
/// [`Xrc::clone(&from)`]: Xrc::clone
/// [fully qualified syntax]: https://doc.rust-lang.org/book/ch19-03-advanced-traits.html#fully-qualified-syntax-for-disambiguation-calling-methods-with-the-same-name
///
/// # Examples
///
/// Sharing some immutable data between threads:
///
// Note that we **do not** run these tests here. The windows builders get super
// unhappy if a thread outlives the main thread and then exits at the same time
// (something deadlocks) so we just avoid this entirely by not running these
// tests.
/// ```no_run
/// use pi_share::xrc::Xrc;
/// use std::thread;
///
/// let five = Xrc::new(5);
///
/// for _ in 0..10 {
///     let five = Xrc::clone(&five);
///
///     thread::spawn(move || {
///         println!("{five:?}");
///     });
/// }
/// ```
///
/// Sharing a mutable [`AtomicUsize`]:
///
/// [`AtomicUsize`]: core::sync::ShareUsize "sync::ShareUsize"
///
/// ```no_run
/// use pi_share::xrc::Xrc;
/// use std::sync::atomic::{AtomicUsize, Ordering};
/// use std::thread;
///
/// let val = Xrc::new(AtomicUsize::new(5));
///
/// for _ in 0..10 {
///     let val = Xrc::clone(&val);
///
///     thread::spawn(move || {
///         let v = val.fetch_add(1, Ordering::SeqCst);
///         println!("{v:?}");
///     });
/// }
/// ```
///
/// See the [`rc` documentation][rc_examples] for more examples of reference
/// counting in general.
///
/// [rc_examples]: crate::rc#examples
pub struct Xrc<T: ?Sized> {
    ptr: NonNull<XrcInner<T>>,
    phantom: PhantomData<XrcInner<T>>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Xrc<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Xrc<T> {}

impl<T: RefUnwindSafe + ?Sized> UnwindSafe for Xrc<T> {}

impl<T: ?Sized> Xrc<T> {
    unsafe fn from_inner(ptr: NonNull<XrcInner<T>>) -> Self {
        Self {
            ptr,
            phantom: PhantomData,
        }
    }

    unsafe fn from_ptr(ptr: *mut XrcInner<T>) -> Self {
        unsafe { Self::from_inner(NonNull::new_unchecked(ptr)) }
    }
}

/// `Weak` is a version of [`Xrc`] that holds a non-owning reference to the
/// managed allocation. The allocation is accessed by calling [`upgrade`] on the `Weak`
/// pointer, which returns an <code>[Option]<[Xrc]\<T>></code>.
///
/// Since a `Weak` reference does not count towards ownership, it will not
/// prevent the value stored in the allocation from being dropped, and `Weak` itself makes no
/// guarantees about the value still being present. Thus it may return [`None`]
/// when [`upgrade`]d. Note however that a `Weak` reference *does* prevent the allocation
/// itself (the backing store) from being deallocated.
///
/// A `Weak` pointer is useful for keeping a temporary reference to the allocation
/// managed by [`Xrc`] without preventing its inner value from being dropped. It is also used to
/// prevent circular references between [`Xrc`] pointers, since mutual owning references
/// would never allow either [`Xrc`] to be dropped. For example, a tree could
/// have strong [`Xrc`] pointers from parent nodes to children, and `Weak`
/// pointers from children back to their parents.
///
/// The typical way to obtain a `Weak` pointer is to call [`Xrc::downgrade`].
///
/// [`upgrade`]: Weak::upgrade
pub struct Weak<T: ?Sized> {
    // This is a `NonNull` to allow optimizing the size of this type in enums,
    // but it is not necessarily a valid pointer.
    // `Weak::new` sets this to `usize::MAX` so that it doesn’t need
    // to allocate space on the heap. That's not a value a real pointer
    // will ever have because RcBox has alignment at least 2.
    // This is only possible when `T: Sized`; unsized `T` never dangle.
    ptr: NonNull<XrcInner<T>>,
}

unsafe impl<T: ?Sized + Sync + Send> Send for Weak<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for Weak<T> {}

impl<T: ?Sized> fmt::Debug for Weak<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(Weak)")
    }
}

// This is repr(C) to future-proof against possible field-reordering, which
// would interfere with otherwise safe [into|from]_raw() of transmutable
// inner types.
#[repr(C)]
struct XrcInner<T: ?Sized> {
    strong: ShareUsize,

    // the value usize::MAX acts as a sentinel for temporarily "locking" the
    // ability to upgrade weak pointers or downgrade strong ones; this is used
    // to avoid races in `make_mut` and `get_mut`.
    weak: ShareUsize,

    data: T,
}

/// Calculate layout for `XrcInner<T>` using the inner value's layout
fn xrcinner_layout_for_value_layout(layout: Layout) -> Layout {
    // Calculate layout using the given value layout.
    // Previously, layout was calculated on the expression
    // `&*(ptr as *const XrcInner<T>)`, but this created a misaligned
    // reference (see #54908).
    Layout::new::<XrcInner<()>>()
        .extend(layout)
        .unwrap()
        .0
        .pad_to_align()
}

unsafe impl<T: ?Sized + Sync + Send> Send for XrcInner<T> {}
unsafe impl<T: ?Sized + Sync + Send> Sync for XrcInner<T> {}

impl<T> Xrc<T> {
    /// Constructs a new `Xrc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn new(data: T) -> Xrc<T> {
        // Start the weak pointer count as 1 which is the weak pointer that's
        // held by all the strong pointers (kinda), see std/rc.rs for more info
        let x: Box<_> = Box::new(XrcInner {
            strong: ShareUsize::new(1),
            weak: ShareUsize::new(1),
            data,
        });
        unsafe { Self::from_inner(Box::leak(x).into()) }
    }

    /// Constructs a new `Xrc<T>` while giving you a `Weak<T>` to the allocation,
    /// to allow you to construct a `T` which holds a weak pointer to itself.
    ///
    /// Generally, a structure circularly referencing itself, either directly or
    /// indirectly, should not hold a strong reference to itself to prevent a memory leak.
    /// Using this function, you get access to the weak pointer during the
    /// initialization of `T`, before the `Xrc<T>` is created, such that you can
    /// clone and store it inside the `T`.
    ///
    /// `new_cyclic` first allocates the managed allocation for the `Xrc<T>`,
    /// then calls your closure, giving it a `Weak<T>` to this allocation,
    /// and only afterwards completes the construction of the `Xrc<T>` by placing
    /// the `T` returned from your closure into the allocation.
    ///
    /// Since the new `Xrc<T>` is not fully-constructed until `Xrc<T>::new_cyclic`
    /// returns, calling [`upgrade`] on the weak reference inside your closure will
    /// fail and result in a `None` value.
    ///
    /// # Panics
    ///
    /// If `data_fn` panics, the panic is propagated to the caller, and the
    /// temporary [`Weak<T>`] is dropped normally.
    ///
    /// # Example
    ///
    /// ```
    /// # #![allow(dead_code)]
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// struct Gadget {
    ///     me: Weak<Gadget>,
    /// }
    ///
    /// impl Gadget {
    ///     /// Construct a reference counted Gadget.
    ///     fn new() -> Xrc<Self> {
    ///         // `me` is a `Weak<Gadget>` pointing at the new allocation of the
    ///         // `Xrc` we're constructing.
    ///         Xrc::new_cyclic(|me| {
    ///             // Create the actual struct here.
    ///             Gadget { me: me.clone() }
    ///         })
    ///     }
    ///
    ///     /// Return a reference counted pointer to Self.
    ///     fn me(&self) -> Xrc<Self> {
    ///         self.me.upgrade().unwrap()
    ///     }
    /// }
    /// ```
    /// [`upgrade`]: Weak::upgrade
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn new_cyclic<F>(data_fn: F) -> Xrc<T>
    where
        F: FnOnce(&Weak<T>) -> T,
    {
        // Construct the inner in the "uninitialized" state with a single
        // weak reference.

        let uninit_ptr: NonNull<_> = Box::leak(Box::new(XrcInner {
            strong: ShareUsize::new(0),
            weak: ShareUsize::new(1),
            data: MaybeUninit::<T>::uninit(),
        }))
        .into();
        let init_ptr: NonNull<XrcInner<T>> = uninit_ptr.cast();

        let weak = Weak { ptr: init_ptr };

        // It's important we don't give up ownership of the weak pointer, or
        // else the memory might be freed by the time `data_fn` returns. If
        // we really wanted to pass ownership, we could create an additional
        // weak pointer for ourselves, but this would result in additional
        // updates to the weak reference count which might not be necessary
        // otherwise.
        let data = data_fn(&weak);

        // Now we can properly initialize the inner value and turn our weak
        // reference into a strong reference.
        let strong = unsafe {
            let inner = init_ptr.as_ptr();
            ptr::write(ptr::addr_of_mut!((*inner).data), data);

            // The above write to the data field must be visible to any threads which
            // observe a non-zero strong count. Therefore we need at least "Release" ordering
            // in order to synchronize with the `compare_exchange_weak` in `Weak::upgrade`.
            //
            // "Acquire" ordering is not required. When considering the possible behaviours
            // of `data_fn` we only need to look at what it could do with a reference to a
            // non-upgradeable `Weak`:
            // - It can *clone* the `Weak`, increasing the weak reference count.
            // - It can drop those clones, decreasing the weak reference count (but never to zero).
            //
            // These side effects do not impact us in any way, and no other side effects are
            // possible with safe code alone.
            let prev_value = (*inner).strong.fetch_add(1, Release);
            debug_assert_eq!(prev_value, 0, "No prior strong references should exist");

            Xrc::from_inner(init_ptr)
        };

        // Strong references should collectively own a shared weak reference,
        // so don't run the destructor for our old weak reference.
        forget(weak);
        strong
    }

    /// Constructs a new `Xrc` with uninitialized contents.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut five = Xrc::<u32>::new_uninit();
    ///
    /// // Deferred initialization:
    /// Xrc::get_mut(&mut five).unwrap().write(5);
    ///
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_uninit() -> Xrc<MaybeUninit<T>> {
        unsafe {
            Xrc::from_ptr(Xrc::allocate_for_layout(
                Layout::new::<T>(),
                |layout| Global.allocate(layout),
                |mem| mem as *mut XrcInner<MaybeUninit<T>>,
            ))
        }
    }

    /// Constructs a new `Xrc` with uninitialized contents, with the memory
    /// being filled with `0` bytes.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let zero = Xrc::<u32>::new_zeroed();
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0)
    /// ```
    ///
    /// [zeroed]: MaybeUninit::zeroed
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_zeroed() -> Xrc<MaybeUninit<T>> {
        unsafe {
            Xrc::from_ptr(Xrc::allocate_for_layout(
                Layout::new::<T>(),
                |layout| Global.allocate_zeroed(layout),
                |mem| mem as *mut XrcInner<MaybeUninit<T>>,
            ))
        }
    }

    /// Constructs a new `Pin<Xrc<T>>`. If `T` does not implement `Unpin`, then
    /// `data` will be pinned in memory and unable to be moved.
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn pin(data: T) -> Pin<Xrc<T>> {
        unsafe { Pin::new_unchecked(Xrc::new(data)) }
    }

    /// Constructs a new `Pin<Xrc<T>>`, return an error if allocation fails.
    #[inline]
    pub fn try_pin(data: T) -> Result<Pin<Xrc<T>>, AllocError> {
        unsafe { Ok(Pin::new_unchecked(Xrc::try_new(data)?)) }
    }

    /// Constructs a new `Xrc<T>`, returning an error if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(allocator_api)]
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::try_new(5)?;
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    #[inline]
    pub fn try_new(data: T) -> Result<Xrc<T>, AllocError> {
        // Start the weak pointer count as 1 which is the weak pointer that's
        // held by all the strong pointers (kinda), see std/rc.rs for more info
        let x: Box<_> = Box::try_new(XrcInner {
            strong: ShareUsize::new(1),
            weak: ShareUsize::new(1),
            data,
        })?;
        unsafe { Ok(Self::from_inner(Box::leak(x).into())) }
    }

    /// Constructs a new `Xrc` with uninitialized contents, returning an error
    /// if allocation fails.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit, allocator_api)]
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut five = Xrc::<u32>::try_new_uninit()?;
    ///
    /// // Deferred initialization:
    /// Xrc::get_mut(&mut five).unwrap().write(5);
    ///
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    // #[unstable(feature = "new_uninit", issue = "63291")]
    pub fn try_new_uninit() -> Result<Xrc<MaybeUninit<T>>, AllocError> {
        unsafe {
            Ok(Xrc::from_ptr(Xrc::try_allocate_for_layout(
                Layout::new::<T>(),
                |layout| Global.allocate(layout),
                |mem| mem as *mut XrcInner<MaybeUninit<T>>,
            )?))
        }
    }

    /// Constructs a new `Xrc` with uninitialized contents, with the memory
    /// being filled with `0` bytes, returning an error if allocation fails.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and incorrect usage
    /// of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit, allocator_api)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let zero = Xrc::<u32>::try_new_zeroed()?;
    /// let zero = unsafe { zero.assume_init() };
    ///
    /// assert_eq!(*zero, 0);
    /// # Ok::<(), std::alloc::AllocError>(())
    /// ```
    ///
    /// [zeroed]: MaybeUninit::zeroed
    // #[unstable(feature = "new_uninit", issue = "63291")]
    pub fn try_new_zeroed() -> Result<Xrc<MaybeUninit<T>>, AllocError> {
        unsafe {
            Ok(Xrc::from_ptr(Xrc::try_allocate_for_layout(
                Layout::new::<T>(),
                |layout| Global.allocate_zeroed(layout),
                |mem| mem as *mut XrcInner<MaybeUninit<T>>,
            )?))
        }
    }
    /// Returns the inner value, if the `Xrc` has exactly one strong reference.
    ///
    /// Otherwise, an [`Err`] is returned with the same `Xrc` that was
    /// passed in.
    ///
    /// This will succeed even if there are outstanding weak references.
    ///
    /// It is strongly recommended to use [`Xrc::into_inner`] instead if you don't
    /// want to keep the `Xrc` in the [`Err`] case.
    /// Immediately dropping the [`Err`] payload, like in the expression
    /// `Xrc::try_unwrap(this).ok()`, can still cause the strong count to
    /// drop to zero and the inner value of the `Xrc` to be dropped:
    /// For instance if two threads each execute this expression in parallel, then
    /// there is a race condition. The threads could first both check whether they
    /// have the last clone of their `Xrc` via `Xrc::try_unwrap`, and then
    /// both drop their `Xrc` in the call to [`ok`][`Result::ok`],
    /// taking the strong count from two down to zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x = Xrc::new(3);
    /// assert_eq!(Xrc::try_unwrap(x), Ok(3));
    ///
    /// let x = Xrc::new(4);
    /// let _y = Xrc::clone(&x);
    /// assert_eq!(*Xrc::try_unwrap(x).unwrap_err(), 4);
    /// ```
    #[inline]
    pub fn try_unwrap(this: Self) -> Result<T, Self> {
        if this
            .inner()
            .strong
            .compare_exchange(1, 0, Relaxed, Relaxed)
            .is_err()
        {
            return Err(this);
        }

        this.inner().strong.load(Acquire);

        unsafe {
            let elem = ptr::read(&this.ptr.as_ref().data);

            // Make a weak pointer to clean up the implicit strong-weak reference
            let _weak = Weak { ptr: this.ptr };
            forget(this);

            Ok(elem)
        }
    }

    /// Returns the inner value, if the `Xrc` has exactly one strong reference.
    ///
    /// Otherwise, [`None`] is returned and the `Xrc` is dropped.
    ///
    /// This will succeed even if there are outstanding weak references.
    ///
    /// If `Xrc::into_inner` is called on every clone of this `Xrc`,
    /// it is guaranteed that exactly one of the calls returns the inner value.
    /// This means in particular that the inner value is not dropped.
    ///
    /// The similar expression `Xrc::try_unwrap(this).ok()` does not
    /// offer such a guarantee. See the last example below
    /// and the documentation of [`Xrc::try_unwrap`].
    ///
    /// # Examples
    ///
    /// Minimal example demonstrating the guarantee that `Xrc::into_inner` gives.
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x = Xrc::new(3);
    /// let y = Xrc::clone(&x);
    ///
    /// // Two threads calling `Xrc::into_inner` on both clones of an `Xrc`:
    /// let x_thread = std::thread::spawn(|| Xrc::into_inner(x));
    /// let y_thread = std::thread::spawn(|| Xrc::into_inner(y));
    ///
    /// let x_inner_value = x_thread.join().unwrap();
    /// let y_inner_value = y_thread.join().unwrap();
    ///
    /// // One of the threads is guaranteed to receive the inner value:
    /// assert!(matches!(
    ///     (x_inner_value, y_inner_value),
    ///     (None, Some(3)) | (Some(3), None)
    /// ));
    /// // The result could also be `(None, None)` if the threads called
    /// // `Xrc::try_unwrap(x).ok()` and `Xrc::try_unwrap(y).ok()` instead.
    /// ```
    ///
    /// A more practical example demonstrating the need for `Xrc::into_inner`:
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// // Definition of a simple singly linked list using `Xrc`:
    /// #[derive(Clone)]
    /// struct LinkedList<T>(Option<Xrc<Node<T>>>);
    /// struct Node<T>(T, Option<Xrc<Node<T>>>);
    ///
    /// // Dropping a long `LinkedList<T>` relying on the destructor of `Xrc`
    /// // can cause a stack overflow. To prevent this, we can provide a
    /// // manual `Drop` implementation that does the destruction in a loop:
    /// impl<T> Drop for LinkedList<T> {
    ///     fn drop(&mut self) {
    ///         let mut link = self.0.take();
    ///         while let Some(Xrc_node) = link.take() {
    ///             if let Some(Node(_value, next)) = Xrc::into_inner(Xrc_node) {
    ///                 link = next;
    ///             }
    ///         }
    ///     }
    /// }
    ///
    /// // Implementation of `new` and `push` omitted
    /// impl<T> LinkedList<T> {
    ///     /* ... */
    /// #   fn new() -> Self {
    /// #       LinkedList(None)
    /// #   }
    /// #   fn push(&mut self, x: T) {
    /// #       self.0 = Some(Xrc::new(Node(x, self.0.take())));
    /// #   }
    /// }
    ///
    /// // The following code could have still caused a stack overflow
    /// // despite the manual `Drop` impl if that `Drop` impl had used
    /// // `Xrc::try_unwrap(Xrc).ok()` instead of `Xrc::into_inner(Xrc)`.
    ///
    /// // Create a long list and clone it
    /// let mut x = LinkedList::new();
    /// for i in 0..100000 {
    ///     x.push(i); // Adds i to the front of x
    /// }
    /// let y = x.clone();
    ///
    /// // Drop the clones in parallel
    /// let x_thread = std::thread::spawn(|| drop(x));
    /// let y_thread = std::thread::spawn(|| drop(y));
    /// x_thread.join().unwrap();
    /// y_thread.join().unwrap();
    /// ```
    #[inline]
    pub fn into_inner(this: Self) -> Option<T> {
        // Make sure that the ordinary `Drop` implementation isn’t called as well
        let mut this = ManuallyDrop::new(this);

        // Following the implementation of `drop` and `drop_slow`
        if this.inner().strong.fetch_sub(1, Release) != 1 {
            return None;
        }

        this.inner().strong.load(Acquire);

        // SAFETY: This mirrors the line
        //
        //     unsafe { ptr::drop_in_place(Self::get_mut_unchecked(self)) };
        //
        // in `drop_slow`. Instead of dropping the value behind the pointer,
        // it is read and eventually returned; `ptr::read` has the same
        // safety conditions as `ptr::drop_in_place`.
        let inner = unsafe { ptr::read(Self::get_mut_unchecked(&mut this)) };

        drop(Weak { ptr: this.ptr });

        Some(inner)
    }
}

impl<T> Xrc<[T]> {
    /// Constructs a new atomically reference-counted slice with uninitialized contents.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut values = Xrc::<[u32]>::new_uninit_slice(3);
    ///
    /// // Deferred initialization:
    /// let data = Xrc::get_mut(&mut values).unwrap();
    /// data[0].write(1);
    /// data[1].write(2);
    /// data[2].write(3);
    ///
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_uninit_slice(len: usize) -> Xrc<[MaybeUninit<T>]> {
        unsafe { Xrc::from_ptr(Xrc::allocate_for_slice(len)) }
    }

    /// Constructs a new atomically reference-counted slice with uninitialized contents, with the memory being
    /// filled with `0` bytes.
    ///
    /// See [`MaybeUninit::zeroed`][zeroed] for examples of correct and
    /// incorrect usage of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let values = Xrc::<[u32]>::new_zeroed_slice(3);
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [0, 0, 0])
    /// ```
    ///
    /// [zeroed]: MaybeUninit::zeroed
    #[cfg(not(no_global_oom_handling))]
    #[must_use]
    pub fn new_zeroed_slice(len: usize) -> Xrc<[MaybeUninit<T>]> {
        unsafe {
            Xrc::from_ptr(Xrc::allocate_for_layout(
                Layout::array::<T>(len).unwrap(),
                |layout| Global.allocate_zeroed(layout),
                |mem| {
                    ptr::slice_from_raw_parts_mut(mem as *mut T, len)
                        as *mut XrcInner<[MaybeUninit<T>]>
                },
            ))
        }
    }
}

impl<T> Xrc<MaybeUninit<T>> {
    /// Converts to `Xrc<T>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut five = Xrc::<u32>::new_uninit();
    ///
    /// // Deferred initialization:
    /// Xrc::get_mut(&mut five).unwrap().write(5);
    ///
    /// let five = unsafe { five.assume_init() };
    ///
    /// assert_eq!(*five, 5)
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub unsafe fn assume_init(self) -> Xrc<T> {
        unsafe { Xrc::from_inner(ManuallyDrop::new(self).ptr.cast()) }
    }
}

impl<T> Xrc<[MaybeUninit<T>]> {
    /// Converts to `Xrc<[T]>`.
    ///
    /// # Safety
    ///
    /// As with [`MaybeUninit::assume_init`],
    /// it is up to the caller to guarantee that the inner value
    /// really is in an initialized state.
    /// Calling this when the content is not yet fully initialized
    /// causes immediate undefined behavior.
    ///
    /// [`MaybeUninit::assume_init`]: MaybeUninit::assume_init
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(new_uninit)]
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut values = Xrc::<[u32]>::new_uninit_slice(3);
    ///
    /// // Deferred initialization:
    /// let data = Xrc::get_mut(&mut values).unwrap();
    /// data[0].write(1);
    /// data[1].write(2);
    /// data[2].write(3);
    ///
    /// let values = unsafe { values.assume_init() };
    ///
    /// assert_eq!(*values, [1, 2, 3])
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    #[inline]
    pub unsafe fn assume_init(self) -> Xrc<[T]> {
        unsafe { Xrc::from_ptr(ManuallyDrop::new(self).ptr.as_ptr() as _) }
    }
}

impl<T: ?Sized> Xrc<T> {
    /// Consumes the `Xrc`, returning the wrapped pointer.
    ///
    /// To avoid a memory leak the pointer must be converted back to an `Xrc` using
    /// [`Xrc::from_raw`].
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x = Xrc::new("hello".to_owned());
    /// let x_ptr = Xrc::into_raw(x);
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[must_use = "losing the pointer will leak memory"]
    pub fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        forget(this);
        ptr
    }

    /// Provides a raw pointer to the data.
    ///
    /// The counts are not affected in any way and the `Xrc` is not consumed. The pointer is valid for
    /// as long as there are strong counts in the `Xrc`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x = Xrc::new("hello".to_owned());
    /// let y = Xrc::clone(&x);
    /// let x_ptr = Xrc::as_ptr(&x);
    /// assert_eq!(x_ptr, Xrc::as_ptr(&y));
    /// assert_eq!(unsafe { &*x_ptr }, "hello");
    /// ```
    #[must_use]
    pub fn as_ptr(this: &Self) -> *const T {
        let ptr: *mut XrcInner<T> = NonNull::as_ptr(this.ptr);

        // SAFETY: This cannot go through Deref::deref or RcBoxPtr::inner because
        // this is required to retain raw/mut provenance such that e.g. `get_mut` can
        // write through the pointer after the Rc is recovered through `from_raw`.
        unsafe { ptr::addr_of_mut!((*ptr).data) }
    }

    /// Constructs an `Xrc<T>` from a raw pointer.
    ///
    /// The raw pointer must have been previously returned by a call to
    /// [`Xrc<U>::into_raw`][into_raw] where `U` must have the same size and
    /// alignment as `T`. This is trivially true if `U` is `T`.
    /// Note that if `U` is not `T` but has the same size and alignment, this is
    /// basically like transmuting references of different types. See
    /// [`mem::transmute`][transmute] for more information on what
    /// restrictions apply in this case.
    ///
    /// The user of `from_raw` has to make sure a specific value of `T` is only
    /// dropped once.
    ///
    /// This function is unsafe because improper use may lead to memory unsafety,
    /// even if the returned `Xrc<T>` is never accessed.
    ///
    /// [into_raw]: Xrc::into_raw
    /// [transmute]: core::mem::transmute
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x = Xrc::new("hello".to_owned());
    /// let x_ptr = Xrc::into_raw(x);
    ///
    /// unsafe {
    ///     // Convert back to an `Xrc` to prevent leak.
    ///     let x = Xrc::from_raw(x_ptr);
    ///     assert_eq!(&*x, "hello");
    ///
    ///     // Further calls to `Xrc::from_raw(x_ptr)` would be memory-unsafe.
    /// }
    ///
    /// // The memory was freed when `x` went out of scope above, so `x_ptr` is now dangling!
    /// ```
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        unsafe {
            let offset = data_offset(ptr);

            // Reverse the offset to find the original XrcInner.
            let xrc_ptr = ptr.byte_sub(offset) as *mut XrcInner<T>;

            Self::from_ptr(xrc_ptr)
        }
    }

    /// Creates a new [`Weak`] pointer to this allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// let weak_five = Xrc::downgrade(&five);
    /// ```
    #[must_use = "this returns a new `Weak` pointer, \
                  without modifying the original `Xrc`"]
    pub fn downgrade(this: &Self) -> Weak<T> {
        // This Relaxed is OK because we're checking the value in the CAS
        // below.
        let mut cur = this.inner().weak.load(Relaxed);

        loop {
            // check if the weak counter is currently "locked"; if so, spin.
            if cur == usize::MAX {
                hint::spin_loop();
                cur = this.inner().weak.load(Relaxed);
                continue;
            }

            // We can't allow the refcount to increase much past `MAX_REFCOUNT`.
            assert!(cur <= MAX_REFCOUNT, "{}", INTERNAL_OVERFLOW_ERROR);

            // NOTE: this code currently ignores the possibility of overflow
            // into usize::MAX; in general both Rc and Xrc need to be adjusted
            // to deal with overflow.

            // Unlike with Clone(), we need this to be an Acquire read to
            // synchronize with the write coming from `is_unique`, so that the
            // events prior to that write happen before this read.
            match this
                .inner()
                .weak
                .compare_exchange_weak(cur, cur + 1, Acquire, Relaxed)
            {
                Ok(_) => {
                    // Make sure we do not create a dangling Weak
                    debug_assert!(!is_dangling(this.ptr.as_ptr()));
                    return Weak { ptr: this.ptr };
                }
                Err(old) => cur = old,
            }
        }
    }

    /// Gets the number of [`Weak`] pointers to this allocation.
    ///
    /// # Safety
    ///
    /// This method by itself is safe, but using it correctly requires extra care.
    /// Another thread can change the weak count at any time,
    /// including potentially between calling this method and acting on the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    /// let _weak_five = Xrc::downgrade(&five);
    ///
    /// // This assertion is deterministic because we haven't shared
    /// // the `Xrc` or `Weak` between threads.
    /// assert_eq!(1, Xrc::weak_count(&five));
    /// ```
    #[inline]
    #[must_use]
    pub fn weak_count(this: &Self) -> usize {
        let cnt = this.inner().weak.load(Acquire);
        // If the weak count is currently locked, the value of the
        // count was 0 just before taking the lock.
        if cnt == usize::MAX {
            0
        } else {
            cnt - 1
        }
    }

    /// Gets the number of strong (`Xrc`) pointers to this allocation.
    ///
    /// # Safety
    ///
    /// This method by itself is safe, but using it correctly requires extra care.
    /// Another thread can change the strong count at any time,
    /// including potentially between calling this method and acting on the result.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    /// let _also_five = Xrc::clone(&five);
    ///
    /// // This assertion is deterministic because we haven't shared
    /// // the `Xrc` between threads.
    /// assert_eq!(2, Xrc::strong_count(&five));
    /// ```
    #[inline]
    #[must_use]
    pub fn strong_count(this: &Self) -> usize {
        this.inner().strong.load(Acquire)
    }

    /// Increments the strong reference count on the `Xrc<T>` associated with the
    /// provided pointer by one.
    ///
    /// # Safety
    ///
    /// The pointer must have been obtained through `Xrc::into_raw`, and the
    /// associated `Xrc` instance must be valid (i.e. the strong count must be at
    /// least 1) for the duration of this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// unsafe {
    ///     let ptr = Xrc::into_raw(five);
    ///     Xrc::increment_strong_count(ptr);
    ///
    ///     // This assertion is deterministic because we haven't shared
    ///     // the `Xrc` between threads.
    ///     let five = Xrc::from_raw(ptr);
    ///     assert_eq!(2, Xrc::strong_count(&five));
    /// }
    /// ```
    #[inline]
    pub unsafe fn increment_strong_count(ptr: *const T) {
        // Retain Xrc, but don't touch refcount by wrapping in ManuallyDrop
        let xrc = unsafe { ManuallyDrop::new(Xrc::<T>::from_raw(ptr)) };
        // Now increase refcount, but don't drop new refcount either
        let _xrc_clone: ManuallyDrop<_> = xrc.clone();
    }

    /// Decrements the strong reference count on the `Xrc<T>` associated with the
    /// provided pointer by one.
    ///
    /// # Safety
    ///
    /// The pointer must have been obtained through `Xrc::into_raw`, and the
    /// associated `Xrc` instance must be valid (i.e. the strong count must be at
    /// least 1) when invoking this method. This method can be used to release the final
    /// `Xrc` and backing storage, but **should not** be called after the final `Xrc` has been
    /// released.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// unsafe {
    ///     let ptr = Xrc::into_raw(five);
    ///     Xrc::increment_strong_count(ptr);
    ///
    ///     // Those assertions are deterministic because we haven't shared
    ///     // the `Xrc` between threads.
    ///     let five = Xrc::from_raw(ptr);
    ///     assert_eq!(2, Xrc::strong_count(&five));
    ///     Xrc::decrement_strong_count(ptr);
    ///     assert_eq!(1, Xrc::strong_count(&five));
    /// }
    /// ```
    #[inline]
    pub unsafe fn decrement_strong_count(ptr: *const T) {
        unsafe { drop(Xrc::from_raw(ptr)) };
    }

    #[inline]
    fn inner(&self) -> &XrcInner<T> {
        // This unsafety is ok because while this Xrc is alive we're guaranteed
        // that the inner pointer is valid. Furthermore, we know that the
        // `XrcInner` structure itself is `Sync` because the inner data is
        // `Sync` as well, so we're ok loaning out an immutable pointer to these
        // contents.
        unsafe { self.ptr.as_ref() }
    }

    // Non-inlined part of `drop`.
    #[inline(never)]
    unsafe fn drop_slow(&mut self) {
        // Destroy the data at this time, even though we must not free the box
        // allocation itself (there might still be weak pointers lying around).
        unsafe { ptr::drop_in_place(Self::get_mut_unchecked(self)) };

        // Drop the weak ref collectively held by all strong references
        drop(Weak { ptr: self.ptr });
    }

    /// Returns `true` if the two `Xrc`s point to the same allocation in a vein similar to
    /// [`ptr::eq`]. See [that function][`ptr::eq`] for caveats when comparing `dyn Trait` pointers.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    /// let same_five = Xrc::clone(&five);
    /// let other_five = Xrc::new(5);
    ///
    /// assert!(Xrc::ptr_eq(&five, &same_five));
    /// assert!(!Xrc::ptr_eq(&five, &other_five));
    /// ```
    ///
    /// [`ptr::eq`]: core::ptr::eq "ptr::eq"
    #[inline]
    #[must_use]
    pub fn ptr_eq(this: &Self, other: &Self) -> bool {
        this.ptr.as_ptr() == other.ptr.as_ptr()
    }
}

impl<T: ?Sized> Xrc<T> {
    /// Allocates an `XrcInner<T>` with sufficient space for
    /// a possibly-unsized inner value where the value has the layout provided.
    ///
    /// The function `mem_to_Xrcinner` is called with the data pointer
    /// and must return back a (potentially fat)-pointer for the `XrcInner<T>`.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn allocate_for_layout(
        value_layout: Layout,
        allocate: impl FnOnce(Layout) -> Result<NonNull<[u8]>, AllocError>,
        mem_to_xrcinner: impl FnOnce(*mut u8) -> *mut XrcInner<T>,
    ) -> *mut XrcInner<T> {
        let layout = xrcinner_layout_for_value_layout(value_layout);
        unsafe {
            Xrc::try_allocate_for_layout(value_layout, allocate, mem_to_xrcinner)
                .unwrap_or_else(|_| handle_alloc_error(layout))
        }
    }

    /// Allocates an `XrcInner<T>` with sufficient space for
    /// a possibly-unsized inner value where the value has the layout provided,
    /// returning an error if allocation fails.
    ///
    /// The function `mem_to_Xrcinner` is called with the data pointer
    /// and must return back a (potentially fat)-pointer for the `XrcInner<T>`.
    unsafe fn try_allocate_for_layout(
        value_layout: Layout,
        allocate: impl FnOnce(Layout) -> Result<NonNull<[u8]>, AllocError>,
        mem_to_xrcinner: impl FnOnce(*mut u8) -> *mut XrcInner<T>,
    ) -> Result<*mut XrcInner<T>, AllocError> {
        let layout = xrcinner_layout_for_value_layout(value_layout);

        let ptr = allocate(layout)?;

        // Initialize the XrcInner
        let inner = mem_to_xrcinner(ptr.as_non_null_ptr().as_ptr());
        debug_assert_eq!(unsafe { Layout::for_value(&*inner) }, layout);

        unsafe {
            ptr::write(&mut (*inner).strong, ShareUsize::new(1));
            ptr::write(&mut (*inner).weak, ShareUsize::new(1));
        }

        Ok(inner)
    }

    /// Allocates an `XrcInner<T>` with sufficient space for an unsized inner value.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn allocate_for_ptr(ptr: *const T) -> *mut XrcInner<T> {
        // Allocate for the `XrcInner<T>` using the given value.
        unsafe {
            Self::allocate_for_layout(
                Layout::for_value(&*ptr),
                |layout| Global.allocate(layout),
                |mem| mem.with_metadata_of(ptr as *const XrcInner<T>),
            )
        }
    }

    #[cfg(not(no_global_oom_handling))]
    fn from_box(v: Box<T>) -> Xrc<T> {
        unsafe {
            let (box_unique, alloc) = Box::into_unique(v);
            let bptr = box_unique.as_ptr();

            let value_size = size_of_val(&*bptr);
            let ptr = Self::allocate_for_ptr(bptr);

            // Copy value as bytes
            ptr::copy_nonoverlapping(
                bptr as *const T as *const u8,
                &mut (*ptr).data as *mut _ as *mut u8,
                value_size,
            );

            // Free the allocation without dropping its contents
            box_free(box_unique, alloc);

            Self::from_ptr(ptr)
        }
    }
}

impl<T> Xrc<[T]> {
    /// Allocates an `XrcInner<[T]>` with the given length.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn allocate_for_slice(len: usize) -> *mut XrcInner<[T]> {
        unsafe {
            Self::allocate_for_layout(
                Layout::array::<T>(len).unwrap(),
                |layout| Global.allocate(layout),
                |mem| ptr::slice_from_raw_parts_mut(mem as *mut T, len) as *mut XrcInner<[T]>,
            )
        }
    }

    /// Copy elements from slice into newly allocated `Xrc<[T]>`
    ///
    /// Unsafe because the caller must either take ownership or bind `T: Copy`.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn copy_from_slice(v: &[T]) -> Xrc<[T]> {
        unsafe {
            let ptr = Self::allocate_for_slice(v.len());

            ptr::copy_nonoverlapping(v.as_ptr(), &mut (*ptr).data as *mut [T] as *mut T, v.len());

            Self::from_ptr(ptr)
        }
    }

    /// Constructs an `Xrc<[T]>` from an iterator known to be of a certain size.
    ///
    /// Behavior is undefined should the size be wrong.
    #[cfg(not(no_global_oom_handling))]
    unsafe fn from_iter_exact(iter: impl Iterator<Item = T>, len: usize) -> Xrc<[T]> {
        // Panic guard while cloning T elements.
        // In the event of a panic, elements that have been written
        // into the new XrcInner will be dropped, then the memory freed.
        struct Guard<T> {
            mem: NonNull<u8>,
            elems: *mut T,
            layout: Layout,
            n_elems: usize,
        }

        impl<T> Drop for Guard<T> {
            fn drop(&mut self) {
                unsafe {
                    let slice = from_raw_parts_mut(self.elems, self.n_elems);
                    ptr::drop_in_place(slice);

                    Global.deallocate(self.mem, self.layout);
                }
            }
        }

        unsafe {
            let ptr = Self::allocate_for_slice(len);

            let mem = ptr as *mut _ as *mut u8;
            let layout = Layout::for_value(&*ptr);

            // Pointer to first element
            let elems = &mut (*ptr).data as *mut [T] as *mut T;

            let mut guard = Guard {
                mem: NonNull::new_unchecked(mem),
                elems,
                layout,
                n_elems: 0,
            };

            for (i, item) in iter.enumerate() {
                ptr::write(elems.add(i), item);
                guard.n_elems += 1;
            }

            // All clear. Forget the guard so it doesn't free the new XrcInner.
            forget(guard);

            Self::from_ptr(ptr)
        }
    }
}

/// Specialization trait used for `From<&[T]>`.
#[cfg(not(no_global_oom_handling))]
trait XrcFromSlice<T> {
    fn from_slice(slice: &[T]) -> Self;
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone> XrcFromSlice<T> for Xrc<[T]> {
    #[inline]
    default fn from_slice(v: &[T]) -> Self {
        unsafe { Self::from_iter_exact(v.iter().cloned(), v.len()) }
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: Copy> XrcFromSlice<T> for Xrc<[T]> {
    #[inline]
    fn from_slice(v: &[T]) -> Self {
        unsafe { Xrc::copy_from_slice(v) }
    }
}

impl<T: ?Sized> Clone for Xrc<T> {
    /// Makes a clone of the `Xrc` pointer.
    ///
    /// This creates another pointer to the same allocation, increasing the
    /// strong reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// let _ = Xrc::clone(&five);
    /// ```
    #[inline]
    fn clone(&self) -> Xrc<T> {
        // Using a relaxed ordering is alright here, as knowledge of the
        // original reference prevents other threads from erroneously deleting
        // the object.
        //
        // As explained in the [Boost documentation][1], Increasing the
        // reference counter can always be done with memory_order_relaxed: New
        // references to an object can only be formed from an existing
        // reference, and passing an existing reference from one thread to
        // another must already provide any required synchronization.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        let old_size = self.inner().strong.fetch_add(1, Relaxed);

        // However we need to guard against massive refcounts in case someone is `forget`ing
        // Xrcs. If we don't do this the count can overflow and users will use-after free. This
        // branch will never be taken in any realistic program. We abort because such a program is
        // incredibly degenerate, and we don't care to support it.
        //
        // This check is not 100% water-proof: we error when the refcount grows beyond `isize::MAX`.
        // But we do that check *after* having done the increment, so there is a chance here that
        // the worst already happened and we actually do overflow the `usize` counter. However, that
        // requires the counter to grow from `isize::MAX` to `usize::MAX` between the increment
        // above and the `abort` below, which seems exceedingly unlikely.
        //
        // This is a global invariant, and also applies when using a compare-exchange loop to increment
        // counters in other methods.
        // Otherwise, the counter could be brought to an almost-overflow using a compare-exchange loop,
        // and then overflow using a few `fetch_add`s.
        if old_size > MAX_REFCOUNT {
            abort();
        }

        unsafe { Self::from_inner(self.ptr) }
    }
}

impl<T: ?Sized> Deref for Xrc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        &self.inner().data
    }
}

impl<T: ?Sized> Receiver for Xrc<T> {}

impl<T: Clone> Xrc<T> {
    /// Makes a mutable reference into the given `Xrc`.
    ///
    /// If there are other `Xrc` pointers to the same allocation, then `make_mut` will
    /// [`clone`] the inner value to a new allocation to ensure unique ownership.  This is also
    /// referred to as clone-on-write.
    ///
    /// However, if there are no other `Xrc` pointers to this allocation, but some [`Weak`]
    /// pointers, then the [`Weak`] pointers will be dissociated and the inner value will not
    /// be cloned.
    ///
    /// See also [`get_mut`], which will fail rather than cloning the inner value
    /// or dissociating [`Weak`] pointers.
    ///
    /// [`clone`]: Clone::clone
    /// [`get_mut`]: Xrc::get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut data = Xrc::new(5);
    ///
    /// *Xrc::make_mut(&mut data) += 1;         // Won't clone anything
    /// let mut other_data = Xrc::clone(&data); // Won't clone inner data
    /// *Xrc::make_mut(&mut data) += 1;         // Clones inner data
    /// *Xrc::make_mut(&mut data) += 1;         // Won't clone anything
    /// *Xrc::make_mut(&mut other_data) *= 2;   // Won't clone anything
    ///
    /// // Now `data` and `other_data` point to different allocations.
    /// assert_eq!(*data, 8);
    /// assert_eq!(*other_data, 12);
    /// ```
    ///
    /// [`Weak`] pointers will be dissociated:
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut data = Xrc::new(75);
    /// let weak = Xrc::downgrade(&data);
    ///
    /// assert!(75 == *data);
    /// assert!(75 == *weak.upgrade().unwrap());
    ///
    /// *Xrc::make_mut(&mut data) += 1;
    ///
    /// assert!(76 == *data);
    /// assert!(weak.upgrade().is_none());
    /// ```
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub fn make_mut(this: &mut Self) -> &mut T {
        // Note that we hold both a strong reference and a weak reference.
        // Thus, releasing our strong reference only will not, by itself, cause
        // the memory to be deallocated.
        //
        // Use Acquire to ensure that we see any writes to `weak` that happen
        // before release writes (i.e., decrements) to `strong`. Since we hold a
        // weak count, there's no chance the XrcInner itself could be
        // deallocated.
        if this
            .inner()
            .strong
            .compare_exchange(1, 0, Acquire, Relaxed)
            .is_err()
        {
            // Another strong pointer exists, so we must clone.
            // Pre-allocate memory to allow writing the cloned value directly.
            let mut xrc = Self::new_uninit();
            unsafe {
                let data = Xrc::get_mut_unchecked(&mut xrc);
                (**this).write_clone_into_raw(data.as_mut_ptr());
                *this = xrc.assume_init();
            }
        } else if this.inner().weak.load(Relaxed) != 1 {
            // Relaxed suffices in the above because this is fundamentally an
            // optimization: we are always racing with weak pointers being
            // dropped. Worst case, we end up allocated a new Xrc unnecessarily.

            // We removed the last strong ref, but there are additional weak
            // refs remaining. We'll move the contents to a new Xrc, and
            // invalidate the other weak refs.

            // Note that it is not possible for the read of `weak` to yield
            // usize::MAX (i.e., locked), since the weak count can only be
            // locked by a thread with a strong reference.

            // Materialize our own implicit weak pointer, so that it can clean
            // up the XrcInner as needed.
            let _weak = Weak { ptr: this.ptr };

            // Can just steal the data, all that's left is Weaks
            let mut xrc = Self::new_uninit();
            unsafe {
                let data = Xrc::get_mut_unchecked(&mut xrc);
                data.as_mut_ptr().copy_from_nonoverlapping(&**this, 1);
                ptr::write(this, xrc.assume_init());
            }
        } else {
            // We were the sole reference of either kind; bump back up the
            // strong ref count.
            this.inner().strong.store(1, Release);
        }

        // As with `get_mut()`, the unsafety is ok because our reference was
        // either unique to begin with, or became one upon cloning the contents.
        unsafe { Self::get_mut_unchecked(this) }
    }

    /// If we have the only reference to `T` then unwrap it. Otherwise, clone `T` and return the
    /// clone.
    ///
    /// Assuming `Xrc_t` is of type `Xrc<T>`, this function is functionally equivalent to
    /// `(*Xrc_t).clone()`, but will avoid cloning the inner value where possible.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(Xrc_unwrap_or_clone)]
    /// # use std::{ptr, sync::Xrc};
    /// let inner = String::from("test");
    /// let ptr = inner.as_ptr();
    ///
    /// let Xrc = Xrc::new(inner);
    /// let inner = Xrc::unwrap_or_clone(Xrc);
    /// // The inner value was not cloned
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    ///
    /// let Xrc = Xrc::new(inner);
    /// let Xrc2 = Xrc.clone();
    /// let inner = Xrc::unwrap_or_clone(Xrc);
    /// // Because there were 2 references, we had to clone the inner value.
    /// assert!(!ptr::eq(ptr, inner.as_ptr()));
    /// // `Xrc2` is the last reference, so when we unwrap it we get back
    /// // the original `String`.
    /// let inner = Xrc::unwrap_or_clone(Xrc2);
    /// assert!(ptr::eq(ptr, inner.as_ptr()));
    /// ```
    #[inline]
    pub fn unwrap_or_clone(this: Self) -> T {
        Xrc::try_unwrap(this).unwrap_or_else(|xrc| (*xrc).clone())
    }
}

impl<T: ?Sized> Xrc<T> {
    /// Returns a mutable reference into the given `Xrc`, if there are
    /// no other `Xrc` or [`Weak`] pointers to the same allocation.
    ///
    /// Returns [`None`] otherwise, because it is not safe to
    /// mutate a shared value.
    ///
    /// See also [`make_mut`][make_mut], which will [`clone`][clone]
    /// the inner value when there are other `Xrc` pointers.
    ///
    /// [make_mut]: Xrc::make_mut
    /// [clone]: Clone::clone
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut x = Xrc::new(3);
    /// *Xrc::get_mut(&mut x).unwrap() = 4;
    /// assert_eq!(*x, 4);
    ///
    /// let _y = Xrc::clone(&x);
    /// assert!(Xrc::get_mut(&mut x).is_none());
    /// ```
    #[inline]
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        if this.is_unique() {
            // This unsafety is ok because we're guaranteed that the pointer
            // returned is the *only* pointer that will ever be returned to T. Our
            // reference count is guaranteed to be 1 at this point, and we required
            // the Xrc itself to be `mut`, so we're returning the only possible
            // reference to the inner data.
            unsafe { Some(Xrc::get_mut_unchecked(this)) }
        } else {
            None
        }
    }

    /// Returns a mutable reference into the given `Xrc`,
    /// without any check.
    ///
    /// See also [`get_mut`], which is safe and does appropriate checks.
    ///
    /// [`get_mut`]: Xrc::get_mut
    ///
    /// # Safety
    ///
    /// If any other `Xrc` or [`Weak`] pointers to the same allocation exist, then
    /// they must not be dereferenced or have active borrows for the duration
    /// of the returned borrow, and their inner type must be exactly the same as the
    /// inner type of this Rc (including lifetimes). This is trivially the case if no
    /// such pointers exist, for example immediately after `Xrc::new`.
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let mut x = Xrc::new(String::new());
    /// unsafe {
    ///     Xrc::get_mut_unchecked(&mut x).push_str("foo")
    /// }
    /// assert_eq!(*x, "foo");
    /// ```
    /// Other `Xrc` pointers to the same allocation must be to the same type.
    /// ```no_run
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let x: Xrc<str> = Xrc::from("Hello, world!");
    /// let mut y: Xrc<[u8]> = x.clone().into();
    /// unsafe {
    ///     // this is Undefined Behavior, because x's inner type is str, not [u8]
    ///     Xrc::get_mut_unchecked(&mut y).fill(0xff); // 0xff is invalid in UTF-8
    /// }
    /// println!("{}", &*x); // Invalid UTF-8 in a str
    /// ```
    /// Other `Xrc` pointers to the same allocation must be to the exact same type, including lifetimes.
    /// ```no_run
    /// #![feature(get_mut_unchecked)]
    ///
    /// use pi_share::xrc::Xrc;
    ///
    /// let x: Xrc<&str> = Xrc::new("Hello, world!");
    /// {
    ///     let s = String::from("Oh, no!");
    ///     let mut y: Xrc<&str> = x.clone().into();
    ///     unsafe {
    ///         // this is Undefined Behavior, because x's inner type
    ///         // is &'long str, not &'short str
    ///         *Xrc::get_mut_unchecked(&mut y) = &s;
    ///     }
    /// }
    /// println!("{}", &*x); // Use-after-free
    /// ```
    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        // We are careful to *not* create a reference covering the "count" fields, as
        // this would alias with concurrent access to the reference counts (e.g. by `Weak`).
        unsafe { &mut (*this.ptr.as_ptr()).data }
    }

    /// Determine whether this is the unique reference (including weak refs) to
    /// the underlying data.
    ///
    /// Note that this requires locking the weak ref count.
    fn is_unique(&mut self) -> bool {
        // lock the weak pointer count if we appear to be the sole weak pointer
        // holder.
        //
        // The acquire label here ensures a happens-before relationship with any
        // writes to `strong` (in particular in `Weak::upgrade`) prior to decrements
        // of the `weak` count (via `Weak::drop`, which uses release). If the upgraded
        // weak ref was never dropped, the CAS here will fail so we do not care to synchronize.
        if self
            .inner()
            .weak
            .compare_exchange(1, usize::MAX, Acquire, Relaxed)
            .is_ok()
        {
            // This needs to be an `Acquire` to synchronize with the decrement of the `strong`
            // counter in `drop` -- the only access that happens when any but the last reference
            // is being dropped.
            let unique = self.inner().strong.load(Acquire) == 1;

            // The release write here synchronizes with a read in `downgrade`,
            // effectively preventing the above read of `strong` from happening
            // after the write.
            self.inner().weak.store(1, Release); // release the lock
            unique
        } else {
            false
        }
    }
}

impl<T: ?Sized> Drop for Xrc<T> {
    /// Drops the `Xrc`.
    ///
    /// This will decrement the strong reference count. If the strong reference
    /// count reaches zero then the only other references (if any) are
    /// [`Weak`], so we `drop` the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// struct Foo;
    ///
    /// impl Drop for Foo {
    ///     fn drop(&mut self) {
    ///         println!("dropped!");
    ///     }
    /// }
    ///
    /// let foo  = Xrc::new(Foo);
    /// let foo2 = Xrc::clone(&foo);
    ///
    /// drop(foo);    // Doesn't print anything
    /// drop(foo2);   // Prints "dropped!"
    /// ```
    #[inline]
    fn drop(&mut self) {
        // Because `fetch_sub` is already atomic, we do not need to synchronize
        // with other threads unless we are going to delete the object. This
        // same logic applies to the below `fetch_sub` to the `weak` count.
        if self.inner().strong.fetch_sub(1, Release) != 1 {
            return;
        }

        // This fence is needed to prevent reordering of use of the data and
        // deletion of the data. Because it is marked `Release`, the decreasing
        // of the reference count synchronizes with this `Acquire` fence. This
        // means that use of the data happens before decreasing the reference
        // count, which happens before this fence, which happens before the
        // deletion of the data.
        //
        // As explained in the [Boost documentation][1],
        //
        // > It is important to enforce any possible access to the object in one
        // > thread (through an existing reference) to *happen before* deleting
        // > the object in a different thread. This is achieved by a "release"
        // > operation after dropping a reference (any access to the object
        // > through this reference must obviously happened before), and an
        // > "acquire" operation before deleting the object.
        //
        // In particular, while the contents of an Xrc are usually immutable, it's
        // possible to have interior writes to something like a Mutex<T>. Since a
        // Mutex is not acquired when it is deleted, we can't rely on its
        // synchronization logic to make writes in thread A visible to a destructor
        // running in thread B.
        //
        // Also note that the Acquire fence here could probably be replaced with an
        // Acquire load, which could improve performance in highly-contended
        // situations. See [2].
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        // [2]: (https://github.com/rust-lang/rust/pull/41714)
        self.inner().strong.load(Acquire);

        unsafe {
            self.drop_slow();
        }
    }
}

impl Xrc<dyn Any + Send + Sync> {
    /// Attempt to downcast the `Xrc<dyn Any + Send + Sync>` to a concrete type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::any::Any;
    /// use pi_share::xrc::Xrc;
    ///
    /// fn print_if_string(value: Xrc<dyn Any + Send + Sync>) {
    ///     if let Ok(string) = value.downcast::<String>() {
    ///         println!("String ({}): {}", string.len(), string);
    ///     }
    /// }
    ///
    /// let my_string = "Hello World".to_string();
    /// print_if_string(Xrc::new(my_string));
    /// print_if_string(Xrc::new(0i8));
    /// ```
    #[inline]
    pub fn downcast<T>(self) -> Result<Xrc<T>, Self>
    where
        T: Any + Send + Sync,
    {
        if (*self).is::<T>() {
            unsafe {
                let ptr = self.ptr.cast::<XrcInner<T>>();
                forget(self);
                Ok(Xrc::from_inner(ptr))
            }
        } else {
            Err(self)
        }
    }

    /// Downcasts the `Xrc<dyn Any + Send + Sync>` to a concrete type.
    ///
    /// For a safe alternative see [`downcast`].
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(downcast_unchecked)]
    ///
    /// use std::any::Any;
    /// use pi_share::xrc::Xrc;
    ///
    /// let x: Xrc<dyn Any + Send + Sync> = Xrc::new(1_usize);
    ///
    /// unsafe {
    ///     assert_eq!(*x.downcast_unchecked::<usize>(), 1);
    /// }
    /// ```
    ///
    /// # Safety
    ///
    /// The contained value must be of type `T`. Calling this method
    /// with the incorrect type is *undefined behavior*.
    ///
    ///
    /// [`downcast`]: Self::downcast
    #[inline]
    pub unsafe fn downcast_unchecked<T>(self) -> Xrc<T>
    where
        T: Any + Send + Sync,
    {
        unsafe {
            let ptr = self.ptr.cast::<XrcInner<T>>();
            forget(self);
            Xrc::from_inner(ptr)
        }
    }
}

impl<T> Weak<T> {
    /// Constructs a new `Weak<T>`, without allocating any memory.
    /// Calling [`upgrade`] on the return value always gives [`None`].
    ///
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Weak;
    ///
    /// let empty: Weak<i64> = Weak::new();
    /// assert!(empty.upgrade().is_none());
    /// ```
    pub const fn new() -> Weak<T> {
        Weak {
            ptr: unsafe { NonNull::new_unchecked(ptr::invalid_mut::<XrcInner<T>>(usize::MAX)) },
        }
    }
}

/// Helper type to allow accessing the reference counts without
/// making any assertions about the data field.
struct WeakInner<'a> {
    weak: &'a ShareUsize,
    strong: &'a ShareUsize,
}

impl<T: ?Sized> Weak<T> {
    /// Returns a raw pointer to the object `T` pointed to by this `Weak<T>`.
    ///
    /// The pointer is valid only if there are some strong references. The pointer may be dangling,
    /// unaligned or even [`null`] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    /// use std::ptr;
    ///
    /// let strong = Xrc::new("hello".to_owned());
    /// let weak = Xrc::downgrade(&strong);
    /// // Both point to the same object
    /// assert!(ptr::eq(&*strong, weak.as_ptr()));
    /// // The strong here keeps it alive, so we can still access the object.
    /// assert_eq!("hello", unsafe { &*weak.as_ptr() });
    ///
    /// drop(strong);
    /// // But not any more. We can do weak.as_ptr(), but accessing the pointer would lead to
    /// // undefined behaviour.
    /// // assert_eq!("hello", unsafe { &*weak.as_ptr() });
    /// ```
    ///
    /// [`null`]: core::ptr::null "ptr::null"
    #[must_use]
    pub fn as_ptr(&self) -> *const T {
        let ptr: *mut XrcInner<T> = NonNull::as_ptr(self.ptr);

        if is_dangling(ptr) {
            // If the pointer is dangling, we return the sentinel directly. This cannot be
            // a valid payload address, as the payload is at least as aligned as XrcInner (usize).
            ptr as *const T
        } else {
            // SAFETY: if is_dangling returns false, then the pointer is dereferenceable.
            // The payload may be dropped at this point, and we have to maintain provenance,
            // so use raw pointer manipulation.
            unsafe { ptr::addr_of_mut!((*ptr).data) }
        }
    }

    /// Consumes the `Weak<T>` and turns it into a raw pointer.
    ///
    /// This converts the weak pointer into a raw pointer, while still preserving the ownership of
    /// one weak reference (the weak count is not modified by this operation). It can be turned
    /// back into the `Weak<T>` with [`from_raw`].
    ///
    /// The same restrictions of accessing the target of the pointer as with
    /// [`as_ptr`] apply.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// let strong = Xrc::new("hello".to_owned());
    /// let weak = Xrc::downgrade(&strong);
    /// let raw = weak.into_raw();
    ///
    /// assert_eq!(1, Xrc::weak_count(&strong));
    /// assert_eq!("hello", unsafe { &*raw });
    ///
    /// drop(unsafe { Weak::from_raw(raw) });
    /// assert_eq!(0, Xrc::weak_count(&strong));
    /// ```
    ///
    /// [`from_raw`]: Weak::from_raw
    /// [`as_ptr`]: Weak::as_ptr
    pub fn into_raw(self) -> *const T {
        let result = self.as_ptr();
        forget(self);
        result
    }

    /// Converts a raw pointer previously created by [`into_raw`] back into `Weak<T>`.
    ///
    /// This can be used to safely get a strong reference (by calling [`upgrade`]
    /// later) or to deallocate the weak count by dropping the `Weak<T>`.
    ///
    /// It takes ownership of one weak reference (with the exception of pointers created by [`new`],
    /// as these don't own anything; the method still works on them).
    ///
    /// # Safety
    ///
    /// The pointer must have originated from the [`into_raw`] and must still own its potential
    /// weak reference.
    ///
    /// It is allowed for the strong count to be 0 at the time of calling this. Nevertheless, this
    /// takes ownership of one weak reference currently represented as a raw pointer (the weak
    /// count is not modified by this operation) and therefore it must be paired with a previous
    /// call to [`into_raw`].
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// let strong = Xrc::new("hello".to_owned());
    ///
    /// let raw_1 = Xrc::downgrade(&strong).into_raw();
    /// let raw_2 = Xrc::downgrade(&strong).into_raw();
    ///
    /// assert_eq!(2, Xrc::weak_count(&strong));
    ///
    /// assert_eq!("hello", &*unsafe { Weak::from_raw(raw_1) }.upgrade().unwrap());
    /// assert_eq!(1, Xrc::weak_count(&strong));
    ///
    /// drop(strong);
    ///
    /// // Decrement the last weak count.
    /// assert!(unsafe { Weak::from_raw(raw_2) }.upgrade().is_none());
    /// ```
    ///
    /// [`new`]: Weak::new
    /// [`into_raw`]: Weak::into_raw
    /// [`upgrade`]: Weak::upgrade
    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // See Weak::as_ptr for context on how the input pointer is derived.

        let ptr = if is_dangling(ptr as *mut T) {
            // This is a dangling Weak.
            ptr as *mut XrcInner<T>
        } else {
            // Otherwise, we're guaranteed the pointer came from a nondangling Weak.
            // SAFETY: data_offset is safe to call, as ptr references a real (potentially dropped) T.
            let offset = unsafe { data_offset(ptr) };
            // Thus, we reverse the offset to get the whole RcBox.
            // SAFETY: the pointer originated from a Weak, so this offset is safe.
            unsafe { ptr.byte_sub(offset) as *mut XrcInner<T> }
        };

        // SAFETY: we now have recovered the original Weak pointer, so can create the Weak.
        Weak {
            ptr: unsafe { NonNull::new_unchecked(ptr) },
        }
    }
}

impl<T: ?Sized> Weak<T> {
    /// Attempts to upgrade the `Weak` pointer to an [`Xrc`], delaying
    /// dropping of the inner value if successful.
    ///
    /// Returns [`None`] if the inner value has since been dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// let weak_five = Xrc::downgrade(&five);
    ///
    /// let strong_five: Option<Xrc<_>> = weak_five.upgrade();
    /// assert!(strong_five.is_some());
    ///
    /// // Destroy all strong pointers.
    /// drop(strong_five);
    /// drop(five);
    ///
    /// assert!(weak_five.upgrade().is_none());
    /// ```
    #[must_use = "this returns a new `Xrc`, \
                  without modifying the original weak pointer"]
    pub fn upgrade(&self) -> Option<Xrc<T>> {
        // We use a CAS loop to increment the strong count instead of a
        // fetch_add as this function should never take the reference count
        // from zero to one.
        self.inner()?
            .strong
            // Relaxed is fine for the failure case because we don't have any expectations about the new state.
            // Acquire is necessary for the success case to synchronise with `Xrc::new_cyclic`, when the inner
            // value can be initialized after `Weak` references have already been created. In that case, we
            // expect to observe the fully initialized value.
            .fetch_update(Acquire, Relaxed, |n| {
                // Any write of 0 we can observe leaves the field in permanently zero state.
                if n == 0 {
                    return None;
                }
                // See comments in `Xrc::clone` for why we do this (for `forget`).
                assert!(n <= MAX_REFCOUNT, "{}", INTERNAL_OVERFLOW_ERROR);
                Some(n + 1)
            })
            .ok()
            // null checked above
            .map(|_| unsafe { Xrc::from_inner(self.ptr) })
    }

    /// Gets the number of strong (`Xrc`) pointers pointing to this allocation.
    ///
    /// If `self` was created using [`Weak::new`], this will return 0.
    pub fn strong_count(&self) -> usize {
        if let Some(inner) = self.inner() {
            inner.strong.load(Acquire)
        } else {
            0
        }
    }

    /// Gets an approximation of the number of `Weak` pointers pointing to this
    /// allocation.
    ///
    /// If `self` was created using [`Weak::new`], or if there are no remaining
    /// strong pointers, this will return 0.
    ///
    /// # Accuracy
    ///
    /// Due to implementation details, the returned value can be off by 1 in
    /// either direction when other threads are manipulating any `Xrc`s or
    /// `Weak`s pointing to the same allocation.
    pub fn weak_count(&self) -> usize {
        self.inner()
            .map(|inner| {
                let weak = inner.weak.load(Acquire);
                let strong = inner.strong.load(Acquire);
                if strong == 0 {
                    0
                } else {
                    // Since we observed that there was at least one strong pointer
                    // after reading the weak count, we know that the implicit weak
                    // reference (present whenever any strong references are alive)
                    // was still around when we observed the weak count, and can
                    // therefore safely subtract it.
                    weak - 1
                }
            })
            .unwrap_or(0)
    }

    /// Returns `None` when the pointer is dangling and there is no allocated `XrcInner`,
    /// (i.e., when this `Weak` was created by `Weak::new`).
    #[inline]
    fn inner(&self) -> Option<WeakInner<'_>> {
        if is_dangling(self.ptr.as_ptr()) {
            None
        } else {
            // We are careful to *not* create a reference covering the "data" field, as
            // the field may be mutated concurrently (for example, if the last `Xrc`
            // is dropped, the data field will be dropped in-place).
            Some(unsafe {
                let ptr = self.ptr.as_ptr();
                WeakInner {
                    strong: &(*ptr).strong,
                    weak: &(*ptr).weak,
                }
            })
        }
    }

    /// Returns `true` if the two `Weak`s point to the same allocation similar to [`ptr::eq`], or if
    /// both don't point to any allocation (because they were created with `Weak::new()`). See [that
    /// function][`ptr::eq`] for caveats when comparing `dyn Trait` pointers.
    ///
    /// # Notes
    ///
    /// Since this compares pointers it means that `Weak::new()` will equal each
    /// other, even though they don't point to any allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let first_rc = Xrc::new(5);
    /// let first = Xrc::downgrade(&first_rc);
    /// let second = Xrc::downgrade(&first_rc);
    ///
    /// assert!(first.ptr_eq(&second));
    ///
    /// let third_rc = Xrc::new(5);
    /// let third = Xrc::downgrade(&third_rc);
    ///
    /// assert!(!first.ptr_eq(&third));
    /// ```
    ///
    /// Comparing `Weak::new`.
    ///
    /// ```
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// let first = Weak::new();
    /// let second = Weak::new();
    /// assert!(first.ptr_eq(&second));
    ///
    /// let third_rc = Xrc::new(());
    /// let third = Xrc::downgrade(&third_rc);
    /// assert!(!first.ptr_eq(&third));
    /// ```
    ///
    /// [`ptr::eq`]: core::ptr::eq "ptr::eq"
    #[inline]
    pub fn ptr_eq(&self, other: &Self) -> bool {
        self.ptr.as_ptr() == other.ptr.as_ptr()
    }
}

impl<T: ?Sized> Clone for Weak<T> {
    /// Makes a clone of the `Weak` pointer that points to the same allocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// let weak_five = Xrc::downgrade(&Xrc::new(5));
    ///
    /// let _ = Weak::clone(&weak_five);
    /// ```
    #[inline]
    fn clone(&self) -> Weak<T> {
        let inner = if let Some(inner) = self.inner() {
            inner
        } else {
            return Weak { ptr: self.ptr };
        };
        // See comments in Xrc::clone() for why this is relaxed. This can use a
        // fetch_add (ignoring the lock) because the weak count is only locked
        // where are *no other* weak pointers in existence. (So we can't be
        // running this code in that case).
        let old_size = inner.weak.fetch_add(1, Relaxed);

        // See comments in Xrc::clone() for why we do this (for forget).
        if old_size > MAX_REFCOUNT {
            abort();
        }

        Weak { ptr: self.ptr }
    }
}

impl<T> Default for Weak<T> {
    /// Constructs a new `Weak<T>`, without allocating memory.
    /// Calling [`upgrade`] on the return value always
    /// gives [`None`].
    ///
    /// [`upgrade`]: Weak::upgrade
    ///
    /// # Examples
    ///
    /// ```
    /// use std::sync::Weak;
    ///
    /// let empty: Weak<i64> = Default::default();
    /// assert!(empty.upgrade().is_none());
    /// ```
    fn default() -> Weak<T> {
        Weak::new()
    }
}

impl<T: ?Sized> Drop for Weak<T> {
    /// Drops the `Weak` pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::{Xrc, Weak};
    ///
    /// struct Foo;
    ///
    /// impl Drop for Foo {
    ///     fn drop(&mut self) {
    ///         println!("dropped!");
    ///     }
    /// }
    ///
    /// let foo = Xrc::new(Foo);
    /// let weak_foo = Xrc::downgrade(&foo);
    /// let other_weak_foo = Weak::clone(&weak_foo);
    ///
    /// drop(weak_foo);   // Doesn't print anything
    /// drop(foo);        // Prints "dropped!"
    ///
    /// assert!(other_weak_foo.upgrade().is_none());
    /// ```
    fn drop(&mut self) {
        // If we find out that we were the last weak pointer, then its time to
        // deallocate the data entirely. See the discussion in Xrc::drop() about
        // the memory orderings
        //
        // It's not necessary to check for the locked state here, because the
        // weak count can only be locked if there was precisely one weak ref,
        // meaning that drop could only subsequently run ON that remaining weak
        // ref, which can only happen after the lock is released.
        let inner = if let Some(inner) = self.inner() {
            inner
        } else {
            return;
        };

        if inner.weak.fetch_sub(1, Release) == 1 {
            inner.weak.load(Acquire);
            unsafe { Global.deallocate(self.ptr.cast(), Layout::for_value_raw(self.ptr.as_ptr())) }
        }
    }
}

trait XrcEqIdent<T: ?Sized + PartialEq> {
    fn eq(&self, other: &Xrc<T>) -> bool;
    fn ne(&self, other: &Xrc<T>) -> bool;
}

impl<T: ?Sized + PartialEq> XrcEqIdent<T> for Xrc<T> {
    #[inline]
    default fn eq(&self, other: &Xrc<T>) -> bool {
        **self == **other
    }
    #[inline]
    default fn ne(&self, other: &Xrc<T>) -> bool {
        **self != **other
    }
}

impl<T: ?Sized + PartialEq> PartialEq for Xrc<T> {
    /// Equality for two `Xrc`s.
    ///
    /// Two `Xrc`s are equal if their inner values are equal, even if they are
    /// stored in different allocation.
    ///
    /// If `T` also implements `Eq` (implying reflexivity of equality),
    /// two `Xrc`s that point to the same allocation are always equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five == Xrc::new(5));
    /// ```
    #[inline]
    fn eq(&self, other: &Xrc<T>) -> bool {
        XrcEqIdent::eq(self, other)
    }

    /// Inequality for two `Xrc`s.
    ///
    /// Two `Xrc`s are not equal if their inner values are not equal.
    ///
    /// If `T` also implements `Eq` (implying reflexivity of equality),
    /// two `Xrc`s that point to the same value are always equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five != Xrc::new(6));
    /// ```
    #[inline]
    fn ne(&self, other: &Xrc<T>) -> bool {
        XrcEqIdent::ne(self, other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for Xrc<T> {
    /// Partial comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `partial_cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    /// use std::cmp::Ordering;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert_eq!(Some(Ordering::Less), five.partial_cmp(&Xrc::new(6)));
    /// ```
    fn partial_cmp(&self, other: &Xrc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }

    /// Less-than comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `<` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five < Xrc::new(6));
    /// ```
    fn lt(&self, other: &Xrc<T>) -> bool {
        *(*self) < *(*other)
    }

    /// 'Less than or equal to' comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `<=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five <= Xrc::new(5));
    /// ```
    fn le(&self, other: &Xrc<T>) -> bool {
        *(*self) <= *(*other)
    }

    /// Greater-than comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `>` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five > Xrc::new(4));
    /// ```
    fn gt(&self, other: &Xrc<T>) -> bool {
        *(*self) > *(*other)
    }

    /// 'Greater than or equal to' comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `>=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert!(five >= Xrc::new(5));
    /// ```
    fn ge(&self, other: &Xrc<T>) -> bool {
        *(*self) >= *(*other)
    }
}
impl<T: ?Sized + Ord> Ord for Xrc<T> {
    /// Comparison for two `Xrc`s.
    ///
    /// The two are compared by calling `cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    /// use std::cmp::Ordering;
    ///
    /// let five = Xrc::new(5);
    ///
    /// assert_eq!(Ordering::Less, five.cmp(&Xrc::new(6)));
    /// ```
    fn cmp(&self, other: &Xrc<T>) -> Ordering {
        (**self).cmp(&**other)
    }
}
impl<T: ?Sized + Eq> Eq for Xrc<T> {}

impl<T: ?Sized + fmt::Display> fmt::Display for Xrc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for Xrc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<T: ?Sized> fmt::Pointer for Xrc<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&(&**self as *const T), f)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: Default> Default for Xrc<T> {
    /// Creates a new `Xrc<T>`, with the `Default` value for `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use pi_share::xrc::Xrc;
    ///
    /// let x: Xrc<i32> = Default::default();
    /// assert_eq!(*x, 0);
    /// ```
    fn default() -> Xrc<T> {
        Xrc::new(Default::default())
    }
}

impl<T: ?Sized + Hash> Hash for Xrc<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self).hash(state)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T> From<T> for Xrc<T> {
    /// Converts a `T` into an `Xrc<T>`
    ///
    /// The conversion moves the value into a
    /// newly allocated `Xrc`. It is equivalent to
    /// calling `Xrc::new(t)`.
    ///
    /// # Example
    /// ```rust
    /// # use pi_share::xrc::Xrc;
    /// let x = 5;
    /// let Xrc = Xrc::new(5);
    ///
    /// assert_eq!(Xrc::from(x), Xrc);
    /// ```
    fn from(t: T) -> Self {
        Xrc::new(t)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: Clone> From<&[T]> for Xrc<[T]> {
    /// Allocate a reference-counted slice and fill it by cloning `v`'s items.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let original: &[i32] = &[1, 2, 3];
    /// let shared: Xrc<[i32]> = Xrc::from(original);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(v: &[T]) -> Xrc<[T]> {
        <Self as XrcFromSlice<T>>::from_slice(v)
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<&str> for Xrc<str> {
    /// Allocate a reference-counted `str` and copy `v` into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let shared: Xrc<str> = Xrc::from("eggplant");
    /// assert_eq!("eggplant", &shared[..]);
    /// ```
    #[inline]
    fn from(v: &str) -> Xrc<str> {
        let xrc = Xrc::<[u8]>::from(v.as_bytes());
        unsafe { Xrc::from_raw(Xrc::into_raw(xrc) as *const str) }
    }
}

#[cfg(not(no_global_oom_handling))]
impl From<String> for Xrc<str> {
    /// Allocate a reference-counted `str` and copy `v` into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let unique: String = "eggplant".to_owned();
    /// let shared: Xrc<str> = Xrc::from(unique);
    /// assert_eq!("eggplant", &shared[..]);
    /// ```
    #[inline]
    fn from(v: String) -> Xrc<str> {
        Xrc::from(&v[..])
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T: ?Sized> From<Box<T>> for Xrc<T> {
    /// Move a boxed object to a new, reference-counted allocation.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let unique: Box<str> = Box::from("eggplant");
    /// let shared: Xrc<str> = Xrc::from(unique);
    /// assert_eq!("eggplant", &shared[..]);
    /// ```
    #[inline]
    fn from(v: Box<T>) -> Xrc<T> {
        Xrc::from_box(v)
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T> From<Vec<T>> for Xrc<[T]> {
    /// Allocate a reference-counted slice and move `v`'s items into it.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let unique: Vec<i32> = vec![1, 2, 3];
    /// let shared: Xrc<[i32]> = Xrc::from(unique);
    /// assert_eq!(&[1, 2, 3], &shared[..]);
    /// ```
    #[inline]
    fn from(mut v: Vec<T>) -> Xrc<[T]> {
        unsafe {
            let rc = Xrc::copy_from_slice(&v);
            // Allow the Vec to free its memory, but not destroy its contents
            v.set_len(0);
            rc
        }
    }
}

impl<'a, B> From<Cow<'a, B>> for Xrc<B>
where
    B: ToOwned + ?Sized,
    Xrc<B>: From<&'a B> + From<B::Owned>,
{
    /// Create an atomically reference-counted pointer from
    /// a clone-on-write pointer by copying its content.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use pi_share::xrc::Xrc;
    /// # use std::borrow::Cow;
    /// let cow: Cow<'_, str> = Cow::Borrowed("eggplant");
    /// let shared: Xrc<str> = Xrc::from(cow);
    /// assert_eq!("eggplant", &shared[..]);
    /// ```
    #[inline]
    fn from(cow: Cow<'a, B>) -> Xrc<B> {
        match cow {
            Cow::Borrowed(s) => Xrc::from(s),
            Cow::Owned(s) => Xrc::from(s),
        }
    }
}

impl From<Xrc<str>> for Xrc<[u8]> {
    /// Converts an atomically reference-counted string slice into a byte slice.
    ///
    /// # Example
    ///
    /// ```
    /// # use pi_share::xrc::Xrc;
    /// let string: Xrc<str> = Xrc::from("eggplant");
    /// let bytes: Xrc<[u8]> = Xrc::from(string);
    /// assert_eq!("eggplant".as_bytes(), bytes.as_ref());
    /// ```
    #[inline]
    fn from(rc: Xrc<str>) -> Self {
        // SAFETY: `str` has the same layout as `[u8]`.
        unsafe { Xrc::from_raw(Xrc::into_raw(rc) as *const [u8]) }
    }
}

impl<T, const N: usize> TryFrom<Xrc<[T]>> for Xrc<[T; N]> {
    type Error = Xrc<[T]>;

    fn try_from(boxed_slice: Xrc<[T]>) -> Result<Self, Self::Error> {
        if boxed_slice.len() == N {
            Ok(unsafe { Xrc::from_raw(Xrc::into_raw(boxed_slice) as *mut [T; N]) })
        } else {
            Err(boxed_slice)
        }
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T> FromIterator<T> for Xrc<[T]> {
    /// Takes each element in the `Iterator` and collects it into an `Xrc<[T]>`.
    ///
    /// # Performance characteristics
    ///
    /// ## The general case
    ///
    /// In the general case, collecting into `Xrc<[T]>` is done by first
    /// collecting into a `Vec<T>`. That is, when writing the following:
    ///
    /// ```rust
    /// # use pi_share::xrc::Xrc;
    /// let evens: Xrc<[u8]> = (0..10).filter(|&x| x % 2 == 0).collect();
    /// # assert_eq!(&*evens, &[0, 2, 4, 6, 8]);
    /// ```
    ///
    /// this behaves as if we wrote:
    ///
    /// ```rust
    /// # use pi_share::xrc::Xrc;
    /// let evens: Xrc<[u8]> = (0..10).filter(|&x| x % 2 == 0)
    ///     .collect::<Vec<_>>() // The first set of allocations happens here.
    ///     .into(); // A second allocation for `Xrc<[T]>` happens here.
    /// # assert_eq!(&*evens, &[0, 2, 4, 6, 8]);
    /// ```
    ///
    /// This will allocate as many times as needed for constructing the `Vec<T>`
    /// and then it will allocate once for turning the `Vec<T>` into the `Xrc<[T]>`.
    ///
    /// ## Iterators of known length
    ///
    /// When your `Iterator` implements `TrustedLen` and is of an exact size,
    /// a single allocation will be made for the `Xrc<[T]>`. For example:
    ///
    /// ```rust
    /// # use pi_share::xrc::Xrc;
    /// let evens: Xrc<[u8]> = (0..10).collect(); // Just a single allocation happens here.
    /// # assert_eq!(&*evens, &*(0..10).collect::<Vec<_>>());
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        ToXrcSlice::to_xrc_slice(iter.into_iter())
    }
}

/// Specialization trait used for collecting into `Xrc<[T]>`.
trait ToXrcSlice<T>: Iterator<Item = T> + Sized {
    fn to_xrc_slice(self) -> Xrc<[T]>;
}

#[cfg(not(no_global_oom_handling))]
impl<T, I: Iterator<Item = T>> ToXrcSlice<T> for I {
    default fn to_xrc_slice(self) -> Xrc<[T]> {
        self.collect::<Vec<T>>().into()
    }
}

#[cfg(not(no_global_oom_handling))]
impl<T, I: iter::TrustedLen<Item = T>> ToXrcSlice<T> for I {
    fn to_xrc_slice(self) -> Xrc<[T]> {
        // This is the case for a `TrustedLen` iterator.
        let (low, high) = self.size_hint();
        if let Some(high) = high {
            debug_assert_eq!(
                low,
                high,
                "TrustedLen iterator's size hint is not exact: {:?}",
                (low, high)
            );

            unsafe {
                // SAFETY: We need to ensure that the iterator has an exact length and we have.
                Xrc::from_iter_exact(self, low)
            }
        } else {
            // TrustedLen contract guarantees that `upper_bound == None` implies an iterator
            // length exceeding `usize::MAX`.
            // The default implementation would collect into a vec which would panic.
            // Thus we panic here immediately without invoking `Vec` code.
            panic!("capacity overflow");
        }
    }
}

impl<T: ?Sized> borrow::Borrow<T> for Xrc<T> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> AsRef<T> for Xrc<T> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized> Unpin for Xrc<T> {}

pub(crate) trait WriteCloneIntoRaw: Sized {
    unsafe fn write_clone_into_raw(&self, target: *mut Self);
}

impl<T: Clone> WriteCloneIntoRaw for T {
    #[inline]
    default unsafe fn write_clone_into_raw(&self, target: *mut Self) {
        // Having allocated *first* may allow the optimizer to create
        // the cloned value in-place, skipping the local and move.
        unsafe { target.write(self.clone()) };
    }
}

impl<T: Copy> WriteCloneIntoRaw for T {
    #[inline]
    unsafe fn write_clone_into_raw(&self, target: *mut Self) {
        // We can always copy in-place, without ever involving a local value.
        unsafe { target.copy_from_nonoverlapping(self, 1) };
    }
}

/// Get the offset within an `XrcInner` for the payload behind a pointer.
///
/// # Safety
///
/// The pointer must point to (and have valid metadata for) a previously
/// valid instance of T, but the T is allowed to be dropped.
unsafe fn data_offset<T: ?Sized>(ptr: *const T) -> usize {
    // Align the unsized value to the end of the XrcInner.
    // Because RcBox is repr(C), it will always be the last field in memory.
    // SAFETY: since the only unsized types possible are slices, trait objects,
    // and extern types, the input safety requirement is currently enough to
    // satisfy the requirements of align_of_val_raw; this is an implementation
    // detail of the language that must not be relied upon outside of std.
    unsafe { data_offset_align(align_of_val_raw(ptr)) }
}
pub(crate) fn is_dangling<T: ?Sized>(ptr: *mut T) -> bool {
    (ptr as *mut ()).addr() == usize::MAX
}
pub(crate) unsafe fn box_free<T: ?Sized, A: Allocator>(ptr: Unique<T>, alloc: A) {
    unsafe {
        let size = size_of_val(ptr.as_ref());
        let align = min_align_of_val(ptr.as_ref());
        let layout = Layout::from_size_align_unchecked(size, align);
        alloc.deallocate(From::from(ptr.cast()), layout)
    }
}

#[inline]
fn data_offset_align(align: usize) -> usize {
    let layout = Layout::new::<XrcInner<()>>();
    layout.size() + layout.padding_needed_for(align)
}

impl<T: core::error::Error + ?Sized> core::error::Error for Xrc<T> {
    #[allow(deprecated, deprecated_in_future)]
    fn description(&self) -> &str {
        core::error::Error::description(&**self)
    }

    #[allow(deprecated)]
    fn cause(&self) -> Option<&dyn core::error::Error> {
        core::error::Error::cause(&**self)
    }

    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        core::error::Error::source(&**self)
    }

    fn provide<'a>(&'a self, req: &mut core::any::Demand<'a>) {
        core::error::Error::provide(&**self, req);
    }
}
