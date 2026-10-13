use std::{cell::UnsafeCell, mem, sync::atomic::Ordering};

/// 单线程原子接口的非原子实现。排序参数不产生跨线程同步；不得跨线程共享。
/// 目前仅为指针、布尔值、`u8` 和 `usize` 实现具体操作。
#[derive(Debug)]
pub struct AtomicCell<T: ?Sized>(UnsafeCell<T>);

impl<T> AtomicCell<T> {
    pub const fn new(value: T) -> Self {
        AtomicCell(UnsafeCell::new(value))
    }
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }
}
impl<T: Default> Default for AtomicCell<T> {
    fn default() -> Self {
        AtomicCell::new(Default::default())
    }
}

impl<T> From<T> for AtomicCell<T> {
    fn from(t: T) -> Self {
        AtomicCell::new(t)
    }
}
impl<T> AtomicCell<*mut T> {
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        current: *mut T,
        new: *mut T,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<*mut T, *mut T> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<*mut T, *mut T>
    where
        F: FnMut(*mut T) -> Option<*mut T>,
    {
        let r = unsafe { *&*self.0.get() };
        if let Some(val) = f(r) {
            *{ unsafe { &mut *self.0.get() } } = val;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn into_inner(self) -> *mut T {
        self.0.into_inner()
    }
    #[inline(always)]
    pub fn load(&self, _order: Ordering) -> *mut T {
        unsafe { *&*self.0.get() }
    }
    #[inline(always)]
    pub fn store(&self, val: *mut T, _order: Ordering) {
        *{ unsafe { &mut *self.0.get() } } = val;
    }
    #[inline(always)]
    pub fn swap(&self, mut val: *mut T, _order: Ordering) -> *mut T {
        mem::swap(unsafe { &mut *self.0.get() }, &mut val);
        val
    }
}

impl AtomicCell<bool> {
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        current: bool,
        new: bool,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<bool, bool> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        current: bool,
        new: bool,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<bool, bool> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_and(&self, val: bool, _order: Ordering) -> bool {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r & val;
        r
    }
    #[inline(always)]
    pub fn fetch_nand(&self, val: bool, _order: Ordering) -> bool {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = !(r & val);
        r
    }
    #[inline(always)]
    pub fn fetch_or(&self, val: bool, _order: Ordering) -> bool {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r | val;
        r
    }
    #[inline(always)]
    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<bool, bool>
    where
        F: FnMut(bool) -> Option<bool>,
    {
        let r = unsafe { *&*self.0.get() };
        if let Some(val) = f(r) {
            *{ unsafe { &mut *self.0.get() } } = val;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_xor(&self, val: bool, _order: Ordering) -> bool {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r ^ val;
        r
    }
    #[inline(always)]
    pub fn into_inner(self) -> bool {
        self.0.into_inner()
    }
    #[inline(always)]
    pub fn load(&self, _order: Ordering) -> bool {
        unsafe { *&*self.0.get() }
    }
    #[inline(always)]
    pub fn store(&self, val: bool, _order: Ordering) {
        *{ unsafe { &mut *self.0.get() } } = val;
    }
    #[inline(always)]
    pub fn swap(&self, mut val: bool, _order: Ordering) -> bool {
        mem::swap(unsafe { &mut *self.0.get() }, &mut val);
        val
    }
}

impl AtomicCell<u8> {
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        current: u8,
        new: u8,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<u8, u8> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        current: u8,
        new: u8,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<u8, u8> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_add(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r.wrapping_add(val);
        r
    }
    #[inline(always)]
    pub fn fetch_and(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r & val;
        r
    }
    #[inline(always)]
    pub fn fetch_max(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        if r < val {
            *{ unsafe { &mut *self.0.get() } } = val;
        }
        r
    }
    #[inline(always)]
    pub fn fetch_min(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        if r > val {
            *{ unsafe { &mut *self.0.get() } } = val;
        }
        r
    }
    #[inline(always)]
    pub fn fetch_nand(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = !(r & val);
        r
    }
    #[inline(always)]
    pub fn fetch_or(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r | val;
        r
    }
    #[inline(always)]
    pub fn fetch_sub(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r.wrapping_sub(val);
        r
    }
    #[inline(always)]
    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<u8, u8>
    where
        F: FnMut(u8) -> Option<u8>,
    {
        let r = unsafe { *&*self.0.get() };
        if let Some(val) = f(r) {
            *{ unsafe { &mut *self.0.get() } } = val;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_xor(&self, val: u8, _order: Ordering) -> u8 {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r ^ val;
        r
    }
    #[inline(always)]
    pub fn into_inner(self) -> u8 {
        self.0.into_inner()
    }
    #[inline(always)]
    pub fn load(&self, _order: Ordering) -> u8 {
        unsafe { *&*self.0.get() }
    }
    #[inline(always)]
    pub fn store(&self, val: u8, _order: Ordering) {
        *{ unsafe { &mut *self.0.get() } } = val;
    }
    #[inline(always)]
    pub fn swap(&self, mut val: u8, _order: Ordering) -> u8 {
        mem::swap(unsafe { &mut *self.0.get() }, &mut val);
        val
    }
}

pub trait SharePtr<T> {
    fn compare_exchange(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T>;
    fn compare_exchange_weak(
        &self,
        current: *mut T,
        new: *mut T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<*mut T, *mut T>;
    fn fetch_update<F>(
        &self,
        set_order: Ordering,
        fetch_order: Ordering,
        f: F,
    ) -> Result<*mut T, *mut T>
    where
        F: FnMut(*mut T) -> Option<*mut T>;
    fn into_inner(self) -> *mut T;
    fn load(&self, order: Ordering) -> *mut T;
    fn new(v: *mut T) -> Self;
    fn store(&self, ptr: *mut T, order: Ordering);
    fn swap(&self, ptr: *mut T, order: Ordering) -> *mut T;
}

impl AtomicCell<usize> {
    #[inline(always)]
    pub fn compare_exchange(
        &self,
        current: usize,
        new: usize,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<usize, usize> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn compare_exchange_weak(
        &self,
        current: usize,
        new: usize,
        _success: Ordering,
        _failure: Ordering,
    ) -> Result<usize, usize> {
        let r = unsafe { *&*self.0.get() };
        if r == current {
            *{ unsafe { &mut *self.0.get() } } = new;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_add(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r.wrapping_add(val);
        r
    }
    #[inline(always)]
    pub fn fetch_and(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r & val;
        r
    }
    #[inline(always)]
    pub fn fetch_max(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        if r < val {
            *{ unsafe { &mut *self.0.get() } } = val;
        }
        r
    }
    #[inline(always)]
    pub fn fetch_min(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        if r > val {
            *{ unsafe { &mut *self.0.get() } } = val;
        }
        r
    }
    #[inline(always)]
    pub fn fetch_nand(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = !(r & val);
        r
    }
    #[inline(always)]
    pub fn fetch_or(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r | val;
        r
    }
    #[inline(always)]
    pub fn fetch_sub(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r.wrapping_sub(val);
        r
    }
    #[inline(always)]
    pub fn fetch_update<F>(
        &self,
        _set_order: Ordering,
        _fetch_order: Ordering,
        mut f: F,
    ) -> Result<usize, usize>
    where
        F: FnMut(usize) -> Option<usize>,
    {
        let r = unsafe { *&*self.0.get() };
        if let Some(val) = f(r) {
            *{ unsafe { &mut *self.0.get() } } = val;
            Ok(r)
        } else {
            Err(r)
        }
    }
    #[inline(always)]
    pub fn fetch_xor(&self, val: usize, _order: Ordering) -> usize {
        let r = unsafe { *&*self.0.get() };
        *{ unsafe { &mut *self.0.get() } } = r ^ val;
        r
    }
    #[inline(always)]
    pub fn into_inner(self) -> usize {
        self.0.into_inner()
    }
    #[inline(always)]
    pub fn load(&self, _order: Ordering) -> usize {
        unsafe { *&*self.0.get() }
    }
    #[inline(always)]
    pub fn store(&self, val: usize, _order: Ordering) {
        *{ unsafe { &mut *self.0.get() } } = val;
    }
    #[inline(always)]
    pub fn swap(&self, mut val: usize, _order: Ordering) -> usize {
        mem::swap(unsafe { &mut *self.0.get() }, &mut val);
        val
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_fetch_operations_wrap() {
        let byte = AtomicCell::new(u8::MAX);
        assert_eq!(byte.fetch_add(1, Ordering::Relaxed), u8::MAX);
        assert_eq!(byte.load(Ordering::Relaxed), 0);
        assert_eq!(byte.fetch_sub(1, Ordering::Relaxed), 0);
        assert_eq!(byte.load(Ordering::Relaxed), u8::MAX);

        let word = AtomicCell::new(usize::MAX);
        assert_eq!(word.fetch_add(1, Ordering::Relaxed), usize::MAX);
        assert_eq!(word.load(Ordering::Relaxed), 0);
        assert_eq!(word.fetch_sub(1, Ordering::Relaxed), 0);
        assert_eq!(word.load(Ordering::Relaxed), usize::MAX);
    }
}
