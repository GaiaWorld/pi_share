use crate::cell::{InvalidBorrow, Ref, RefMut, TrustCell};
use std::rc::Rc;
use std::{
    cmp::Ordering,
    fmt,
    hash::{Hash, Hasher},
};

/// 使用标准库 `Rc` 共享 `TrustCell`，仅适用于单线程。
/// 名称保留供现有 `ShareRefCell` 别名及调用方使用，不再依赖自定义 `Xrc`。
pub struct XrcCell<T>(pub Rc<TrustCell<T>>);

impl<T> XrcCell<T> {
    #[inline]
    pub fn new(value: T) -> Self {
        XrcCell(Rc::new(TrustCell::new(value)))
    }
    pub fn ptr_eq(&self, other: &XrcCell<T>) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
    /// 取得只读守卫；存在可变借用时会 panic。
    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.as_ref().borrow()
    }
    /// 尝试取得只读守卫；借用冲突时返回错误。
    pub fn try_borrow(&self) -> Result<Ref<'_, T>, InvalidBorrow> {
        self.0.as_ref().try_borrow()
    }
    /// 取得可变守卫；存在其他借用时会 panic。
    pub fn borrow_mut(&self) -> RefMut<'_, T> {
        self.0.as_ref().borrow_mut()
    }
    /// 尝试取得可变守卫；借用冲突时返回错误。
    pub fn try_borrow_mut(&self) -> Result<RefMut<'_, T>, InvalidBorrow> {
        self.0.as_ref().try_borrow_mut()
    }
}

impl<T> Clone for XrcCell<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: Hash> Hash for XrcCell<T> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (*self.borrow()).hash(state);
    }
}

impl<T: fmt::Display> fmt::Display for XrcCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.borrow()).fmt(f)
    }
}

impl<T: fmt::Debug> fmt::Debug for XrcCell<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self.borrow()).fmt(f)
    }
}

impl<T: PartialEq> PartialEq for XrcCell<T> {
    #[inline]
    fn eq(&self, other: &XrcCell<T>) -> bool {
        self.borrow().eq(&*other.borrow())
    }
}

impl<T: PartialOrd> PartialOrd for XrcCell<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.borrow().partial_cmp(&*other.borrow())
    }
}

impl<T: Eq> Eq for XrcCell<T> {}

impl<T: Ord> Ord for XrcCell<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.borrow().cmp(&*other.borrow())
    }
}

#[test]
fn test_xrc_trustcell() {
    struct A {
        pub a: u32,
    }

    fn read_a(a: &A) -> u32 {
        a.a
    }

    fn add_a(a: &mut A, num: u32) {
        a.a += num;
    }

    let a = XrcCell::new(A { a: 3 });
    add_a(&mut *a.borrow_mut(), 10);
    let b = read_a(&*a.borrow());
    assert_eq!(b, 13);
}

#[test]
fn xrc_cell_formats_inner_value() {
    let cell = XrcCell::new(42);
    assert_eq!(format!("{cell:?}"), "42");
    assert_eq!(format!("{cell}"), "42");
}

#[test]
fn xrc_cell_borrow_guard_blocks_mutation_from_clone() {
    let cell = XrcCell::new(1);
    let clone = cell.clone();
    let read = cell.borrow();
    assert!(clone.try_borrow_mut().is_err());
    assert_eq!(*read, 1);
    drop(read);
    *clone.borrow_mut() = 2;
    assert_eq!(*cell.borrow(), 2);
}
