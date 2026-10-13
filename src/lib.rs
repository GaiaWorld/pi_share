//! 在多线程构建中使用标准库共享指针、锁和原子类型；在确认单线程的构建中
//! 启用 `rc`，以 `Rc`、动态借用检查及非原子操作减少同步开销。
//! 不能仅凭目标是 WebAssembly 就启用 `rc`：有共享内存或多个工作线程时
//! 仍须使用默认模式。各模式的借用与锁定行为并不完全一致。
//!
//! `serial` 只放宽 `ThreadSend` / `ThreadSync` 标记约束；
//! `rc` 会自动启用 `serial`。具体映射、限制和迁移说明见 README。
//!
pub mod arc_cell;
pub mod atomic;
pub mod cell;
pub mod lock;
pub mod xrc_cell;

pub type ShareCell<T> = cell::TrustCell<T>;
pub type Cell<T> = cell::TrustCell<T>;

/// 线程传递约束：默认模式要求 `Send`，`serial` 模式不施加约束。
#[cfg(feature = "serial")]
pub trait ThreadSend {}
#[cfg(feature = "serial")]
impl<T> ThreadSend for T {}
/// 线程共享约束：默认模式要求 `Send + Sync`，`serial` 模式不施加约束。
#[cfg(feature = "serial")]
pub trait ThreadSync {}
#[cfg(feature = "serial")]
impl<T> ThreadSync for T {}

#[cfg(not(feature = "serial"))]
pub trait ThreadSend: Send {}
#[cfg(not(feature = "serial"))]
impl<T: Send> ThreadSend for T {}
#[cfg(not(feature = "serial"))]
pub trait ThreadSync: Sync + Send {}
#[cfg(not(feature = "serial"))]
impl<T: Sync + Send> ThreadSync for T {}

#[cfg(feature = "rc")]
pub type Share<T> = std::rc::Rc<T>;
#[cfg(feature = "rc")]
pub type ShareWeak<T> = std::rc::Weak<T>;
#[cfg(feature = "rc")]
pub type ShareMutex<T> = crate::lock::LockCell<T>;
#[cfg(feature = "rc")]
pub type ShareRwLock<T> = crate::lock::LockCell<T>;
#[cfg(feature = "rc")]
pub type SharePtr<T> = crate::atomic::AtomicCell<T>;
#[cfg(feature = "rc")]
pub type ShareBool = crate::atomic::AtomicCell<bool>;
#[cfg(feature = "rc")]
pub type ShareU8 = crate::atomic::AtomicCell<u8>;
#[cfg(feature = "rc")]
pub type ShareUsize = crate::atomic::AtomicCell<usize>;
#[cfg(feature = "rc")]
pub type ShareU32 = crate::atomic::AtomicCell<u32>;
#[cfg(feature = "rc")]
pub type ShareU64 = crate::atomic::AtomicCell<u64>;
#[cfg(feature = "rc")]
pub use xrc_cell::XrcCell as ShareRefCell;
#[cfg(feature = "rc")]
#[inline(always)]
pub fn fence(_or: std::sync::atomic::Ordering) {}

#[cfg(not(feature = "rc"))]
use std::sync::{
    atomic::{AtomicBool, AtomicPtr, AtomicU32, AtomicU64, AtomicU8, AtomicUsize},
    Arc, Mutex, RwLock, Weak,
};

#[cfg(not(feature = "rc"))]
pub type Share<T> = Arc<T>;
#[cfg(not(feature = "rc"))]
pub type ShareWeak<T> = Weak<T>;
#[cfg(not(feature = "rc"))]
pub type ShareMutex<T> = Mutex<T>;
#[cfg(not(feature = "rc"))]
pub type ShareRwLock<T> = RwLock<T>;
#[cfg(not(feature = "rc"))]
pub type SharePtr<T> = AtomicPtr<T>;
#[cfg(not(feature = "rc"))]
pub type ShareBool = AtomicBool;
#[cfg(not(feature = "rc"))]
pub type ShareU8 = AtomicU8;
#[cfg(not(feature = "rc"))]
pub type ShareUsize = AtomicUsize;
#[cfg(not(feature = "rc"))]
pub type ShareU32 = AtomicU32;
#[cfg(not(feature = "rc"))]
pub type ShareU64 = AtomicU64;
#[cfg(not(feature = "rc"))]
pub use arc_cell::ArcCell as ShareRefCell;
#[cfg(not(feature = "rc"))]
#[inline(always)]
pub fn fence(or: std::sync::atomic::Ordering) {
    std::sync::atomic::fence(or)
}

#[cfg(test)]
mod thread_safety_tests {
    #[cfg(not(feature = "rc"))]
    #[test]
    fn trust_cell_can_be_shared_across_threads() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<crate::ShareCell<usize>>();
    }
}
