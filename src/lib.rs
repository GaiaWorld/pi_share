//! 默认 不带 任何 feature
//!
//! ## 1. 几个类型封装
//!
//! + `Share` = `Xrc` | `Arc`
//! + `ShareWeak` = `xrc::Weak` | `sync::Weak`
//! + `ShareMutex` = `LockCell(RefCell<T>)` | parking_lot::Mutex
//! + `ShareRwLock` = `LockCell(RefCell<T>)` | `parking_lot::RwLock`
//! + `ShareCell` = `cell::TrustCell`
//! + `SharePtr` = `SyncUnsafeCell<T>` | `AtomicPtr<T>`
//! + `ShareRefCell` = `XrcCell<T>` | `ArcCell<T>`
//! + `ShareBool` = `SyncUnsafeCell<bool>` | `AtomicBool`
//! + `ShareU8` = `SyncUnsafeCell<u8>` | `AtomicU8`
//! + `ShareU32` = `SyncUnsafeCell<u32>` | `AtomicU32`
//! + `ShareUsize` = `SyncUnsafeCell<usize>` | `AtomicUsize`
//!
//! ## 2. 提供 Send, Sync 的 封装
//!
//! 目的：wasm 不支持 Send + Sync
//!
//! + ThreadSend = Send
//! + ThreadSync = Sync + Send
//!
#![feature(sync_unsafe_cell)]
#![feature(const_trait_impl)]
#![feature(allocator_api)]
#![feature(receiver_trait)]
#![feature(core_intrinsics)]
#![feature(strict_provenance)]
#![feature(error_in_core)]
#![feature(error_generic_member_access)]
#![feature(provide_any)]
#![feature(layout_for_ptr)]
#![feature(trusted_len)]
#![feature(slice_ptr_get)]
#![feature(ptr_internals)]
#![feature(set_ptr_value)]
#![feature(pointer_byte_offsets)]
#![feature(alloc_layout_extra)]
#![feature(specialization)]

pub mod arc_cell;
pub mod atomic;
pub mod cell;
pub mod lock;
pub mod xrc;
pub mod xrc_cell;


pub type ShareCell<T> = cell::TrustCell<T>;
pub type Cell<T> = cell::TrustCell<T>;

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
pub type Share<T> = Xrc<T>;
#[cfg(feature = "rc")]
pub type ShareWeak<T> = xrc::Weak<T>;
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
pub use xrc_cell::XrcCell as ShareRefCell;
#[cfg(feature = "rc")]
#[inline(always)]
pub fn fence(or: std::sync::atomic::Ordering) {
}

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
pub use arc_cell::ArcCell as ShareRefCell;
#[cfg(not(feature = "rc"))]
#[inline(always)]
pub fn fence(or: std::sync::atomic::Ordering) {
    std::sync::atomic::fence(or)
}