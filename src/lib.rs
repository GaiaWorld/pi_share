//! 默认 不带 任何 feature
//!
//! 提供五个类型：`Share`， `ShareWeak`,，`ShareMutex`, `ShareRwLock`，`ShareCell`.
//!
//! 在feature="rc"时：
//!
//! * `Share`等同于`std::rc::Rc`
//! * `ShareWeak`等同于`std::rc::Weak`
//! * `ShareMutex`等同于`LockCell(RefCell<T>)`
//! * `ShareRwLock`等同于`LockCell(RefCell<T>)`
//! * `ShareCell`等同于`std::cell::RefCell`
//! * `ShareBool`等同于`UnsafeCell<bool>`
//! * `ShareU8`等同于`UnsafeCell<u8>`
//! * `ShareUsize`等同于`UnsafeCell<usize>`
//! * `SharePtr`等同于`UnsafeCell<T>`
//! * `ShareRefCell`等同于`Rc(RefCell<T>)`
//!
//! 在feature="arc"时:
//!
//! * `Share`等同于`std::sync::Arc`,
//! * `ShareWeak`等同于`std::sync::Weak`.
//! * `ShareMutex`等同于`std::sync::Mutex`
//! * `ShareRwLock`等同于`std::sync::RwLock`
//! * `ShareCell`等同于`cell::TrustCell`
//! * `ShareBool`等同于`RefCell<bool>`
//! * `ShareU8`等同于`RefCell<u8>`
//! * `ShareUsize`等同于`RefCell<usize>`
//! * `SharePtr`等同于`RefCell<T>`
//! * `ShareRefCell`等同于`Arc(TrustCell<T>)`

#![feature(const_trait_impl)]

pub mod atomic;
pub mod cell;
pub mod lock;
pub mod rc_refcell;
pub mod arc_trustcell;

#[cfg(feature = "rc")]
use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};
#[cfg(feature = "rc")]
pub type Share<T> = Rc<T>;
#[cfg(feature = "rc")]
pub type ShareWeak<T> = Weak<T>;
#[cfg(feature = "rc")]
pub type ShareMutex<T> = crate::lock::LockCell<T>;
#[cfg(feature = "rc")]
pub type ShareRwLock<T> = crate::lock::LockCell<T>;
#[cfg(feature = "rc")]
pub type ShareCell<T> = RefCell<T>;
#[cfg(feature = "rc")]
pub type SharePtr<T> = crate::atomic::AtomicCell<T>;
#[cfg(feature = "rc")]
pub type ShareBool = crate::atomic::AtomicCell<bool>;
#[cfg(feature = "rc")]
pub type ShareU8 = crate::atomic::AtomicCell<u8>;
#[cfg(feature = "rc")]
pub type ShareUsize = crate::atomic::AtomicCell<usize>;
#[cfg(feature = "rc")]
pub use rc_refcell::RcRefCell as ShareRefCell;

#[cfg(not(feature = "rc"))]
use std::sync::{
    atomic::AtomicBool, atomic::AtomicPtr, atomic::AtomicU8, atomic::AtomicUsize, Arc, Mutex,
    RwLock, Weak,
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
pub type ShareCell<T> = cell::TrustCell<T>;
#[cfg(not(feature = "rc"))]
pub type SharePtr<T> = AtomicPtr<T>;
#[cfg(not(feature = "rc"))]
pub type ShareBool = AtomicBool;
#[cfg(not(feature = "rc"))]
pub type ShareU8 = AtomicU8;
#[cfg(not(feature = "rc"))]
pub type ShareUsize = AtomicUsize;
#[cfg(not(feature = "rc"))]
pub use arc_trustcell::ArcTrustCell as ShareRefCell;