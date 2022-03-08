use crate::cell::TrustCell;
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
    sync::Arc,
};

#[derive(Clone)]
pub struct ArcTrustCell<T>(pub Arc<TrustCell<T>>);

impl<T> ArcTrustCell<T> {
    #[inline]
    pub fn new(value: T) -> Self {
        ArcTrustCell(Arc::new(TrustCell::new(value)))
    }
}

impl<T: Hash> Hash for ArcTrustCell<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl<T: fmt::Display> fmt::Display for ArcTrustCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: fmt::Debug> fmt::Debug for ArcTrustCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.deref().fmt(f)
    }
}

impl<T: PartialEq> PartialEq for ArcTrustCell<T> {
    #[inline]
    fn eq(&self, other: &ArcTrustCell<T>) -> bool {
        self.deref().eq(other)
    }
}

impl<T: PartialOrd> PartialOrd for ArcTrustCell<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Eq> Eq for ArcTrustCell<T> {}

impl<T: Ord> Ord for ArcTrustCell<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T> Deref for ArcTrustCell<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        let r = self.0.as_ref().borrow().deref() as *const T;
        unsafe { std::mem::transmute(r) }
    }
}

impl<T> DerefMut for ArcTrustCell<T> {
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

    let mut a = ArcTrustCell::new(A { a: 3 });
    add_a(a.deref_mut(), 10);
    let b = read_a(a.deref());
    assert_eq!(b, 13);
}
