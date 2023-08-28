//! 默认 不带 任何 feature
//!
//! ## 1. 几个类型封装
//!
//! + `Share` = `Rc` | `Arc`
//! + `ShareWeak` = `rc::Weak` | `sync::Weak`
//! + `ShareMutex` = `LockCell(RefCell<T>)` | parking_lot::Mutex
//! + `ShareRwLock` = `LockCell(RefCell<T>)` | `parking_lot::RwLock`
//! + `ShareCell` = `std::cell::RefCell` | `cell::TrustCell`
//! + `SharePtr` = `UnsafeCell<T>` | `AtomicPtr<T>`
//! + `ShareRefCell` = `Rc(RefCell<T>)` | `Arc(TrustCell<T>)`
//! + `ShareBool` = `UnsafeCell<bool>` | `AtomicBool`
//! + `ShareU8` = `UnsafeCell<u8>` | `AtomicU8`
//! + `ShareU32` = `UnsafeCell<u32>` | `AtomicU32`
//! + `ShareUsize` = `UnsafeCell<usize>` | `AtomicUsize`
//!
//! ## 2. 提供 Send, Sync 的 封装
//!
//! 目的：wasm 不支持 Send + Sync
//!
//! + ThreadSend = Send
//! + ThreadSync = Sync + Send
//!

#![feature(const_trait_impl)]
pub mod arc_trustcell;
pub mod atomic;
pub mod cell;
pub mod lock;
pub mod rc_refcell;

#[cfg(feature = "serial")]
pub trait ThreadSend {}
#[cfg(feature = "serial")]
impl<T> ThreadSend for T {}
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
pub type ShareU32 = crate::atomic::AtomicCell<u32>;
#[cfg(feature = "rc")]
pub use rc_refcell::RcRefCell as ShareRefCell;

#[cfg(feature = "rc")]
pub type Cell<T> = std::cell::RefCell<T>;

#[cfg(not(feature = "rc"))]
use std::sync::{
    atomic::AtomicBool, atomic::AtomicPtr, atomic::AtomicU8, atomic::AtomicUsize, atomic::AtomicU32, Arc, Weak,
};
#[cfg(not(feature = "rc"))]
pub type Share<T> = Arc<T>;
#[cfg(not(feature = "rc"))]
pub type ShareWeak<T> = Weak<T>;
#[cfg(not(feature = "rc"))]
pub type ShareMutex<T> = parking_lot::Mutex<T>;
#[cfg(not(feature = "rc"))]
pub type ShareRwLock<T> = parking_lot::RwLock<T>;
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
pub type ShareU32 = AtomicU32;
#[cfg(not(feature = "rc"))]
pub use arc_trustcell::ArcTrustCell as ShareRefCell;
#[cfg(not(feature = "rc"))]
pub type Cell<T> = crate::cell::TrustCell<T>;
