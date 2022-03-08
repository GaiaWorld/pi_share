use std::{
    rc::Rc,
    cell::RefCell,
    ops::{Deref, DerefMut}
};

pub struct RcRefCell<T>(pub Rc<RefCell<T>>);

impl<T> RcRefCell<T> {
    pub fn new(value: T) -> Self {
        RcRefCell(Rc::new(RefCell::new(value)))
    }
}

impl<T> Deref for RcRefCell<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        let r = self.0.as_ref().borrow().deref() as *const T;
        unsafe { std::mem::transmute(r) }
    }
}

impl<T> DerefMut for RcRefCell<T> {
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

    let mut a = RcRefCell::new(A{a: 3});
    add_a(a.deref_mut(), 10);
    let b = read_a(a.deref());
    assert_eq!(b, 13);
}