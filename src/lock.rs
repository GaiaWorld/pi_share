use crate::cell::{Ref, RefMut, TrustCell};

/// 单线程的动态借用锁；借用冲突立即 panic，`try_*` 返回 `None`，不等待也不中毒。
/// `read`、`write` 和 `lock` 保持与标准锁一致的 `Result` 返回形式。
#[derive(Debug)]
pub struct LockCell<T>(TrustCell<T>);

impl<T> LockCell<T> {
    #[inline]
    pub const fn new(value: T) -> Self {
        LockCell(TrustCell::new(value))
    }
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
    pub fn is_poisoned(&self) -> bool {
        false
    }
}

impl<T> LockCell<T> {
    pub fn get_mut(&mut self) -> RefMut<'_, T> {
        self.0.borrow_mut()
    }
    pub fn read(&self) -> Result<Ref<'_, T>, ()> {
        Ok(self.0.borrow())
    }
    pub fn try_read(&self) -> Option<Ref<'_, T>> {
        match self.0.try_borrow() {
            Ok(r) => Some(r),
            _ => None,
        }
    }
    pub fn write(&self) -> Result<RefMut<'_, T>, ()> {
        Ok(self.0.borrow_mut())
    }
    pub fn try_write(&self) -> Option<RefMut<'_, T>> {
        match self.0.try_borrow_mut() {
            Ok(r) => Some(r),
            _ => None,
        }
    }
    pub fn lock(&self) -> Result<RefMut<'_, T>, ()> {
        Ok(self.0.borrow_mut())
    }
    pub fn try_lock(&self) -> Option<RefMut<'_, T>> {
        match self.0.try_borrow_mut() {
            Ok(r) => Some(r),
            _ => None,
        }
    }
}

impl<T: Default> Default for LockCell<T> {
    fn default() -> Self {
        LockCell::new(Default::default())
    }
}
impl<T> From<T> for LockCell<T> {
    fn from(t: T) -> Self {
        LockCell::new(t)
    }
}
