use crate::cell::{TrustCell, RefMut, InvalidBorrow};
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
    sync::Arc,
};

pub struct ArcCell<T>(pub Arc<TrustCell<T>>);

impl<T> ArcCell<T> {
    #[inline]
    pub fn new(value: T) -> Self {
        ArcCell(Arc::new(TrustCell::new(value)))
    }
    pub fn ptr_eq(&self, other: &ArcCell<T>) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.as_ref().borrow_mut()
    }
    pub fn try_borrow_mut(&self) -> Result<RefMut<T>, InvalidBorrow> {
        self.0.as_ref().try_borrow_mut()
    }
}

impl<T> Clone for ArcCell<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Hash> Hash for ArcCell<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<T: fmt::Display> fmt::Display for ArcCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: fmt::Debug> fmt::Debug for ArcCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: PartialEq> PartialEq for ArcCell<T> {
    #[inline]
    fn eq(&self, other: &ArcCell<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: PartialOrd> PartialOrd for ArcCell<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Eq> Eq for ArcCell<T> {}

impl<T: Ord> Ord for ArcCell<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T> Deref for ArcCell<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        let r = self.0.as_ref().borrow().deref() as *const T;
        unsafe { std::mem::transmute(r) }
    }
}

impl<T> DerefMut for ArcCell<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        let r = self.0.as_ref().borrow_mut().deref_mut() as *mut T;
        unsafe { std::mem::transmute(r) }
    }
}

#[test]
fn test_arc_trustcell() {
    struct A {
        pub a: u32,
    }

    fn read_a(a: &A) -> u32 {
        a.a
    }

    fn add_a(a: &mut A, num: u32) {
        a.a += num;
    }

    let mut a = ArcCell::new(A { a: 3 });
    add_a(a.deref_mut(), 10);
    let b = read_a(a.deref());
    assert_eq!(b, 13);
}
