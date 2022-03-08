use std::{
    cell::RefCell,
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
    rc::Rc,
};

pub struct RcRefCell<T: ?Sized>(pub Rc<RefCell<T>>);

impl<T: Sized> RcRefCell<T> {
    #[inline]
    pub fn new(value: T) -> Self {
        RcRefCell(Rc::new(RefCell::new(value)))
    }
}

impl<T: ?Sized> Clone for RcRefCell<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized + Hash> Hash for RcRefCell<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<T: ?Sized + fmt::Display> fmt::Display for RcRefCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: ?Sized + fmt::Debug> fmt::Debug for RcRefCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: ?Sized + PartialEq> PartialEq for RcRefCell<T> {
    #[inline]
    fn eq(&self, other: &RcRefCell<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: ?Sized + PartialOrd> PartialOrd for RcRefCell<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: ?Sized + Eq> Eq for RcRefCell<T> {}

impl<T: ?Sized + Ord> Ord for RcRefCell<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T: ?Sized> Deref for RcRefCell<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        let r = self.0.as_ref().borrow().deref() as *const T;
        unsafe { std::mem::transmute(r) }
    }
}

impl<T: ?Sized> DerefMut for RcRefCell<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        let r = self.0.as_ref().borrow_mut().deref_mut() as *mut T;
        unsafe { std::mem::transmute(r) }
    }
}

#[test]
fn test_rc_refcell() {
    struct A {
        pub a: u32,
    }

    fn read_a(a: &A) -> u32 {
        a.a
    }

    fn add_a(a: &mut A, num: u32) {
        a.a += num;
    }

    let mut a = RcRefCell::new(A { a: 3 });
    add_a(a.deref_mut(), 10);
    let b = read_a(a.deref());
    assert_eq!(b, 13);
}
