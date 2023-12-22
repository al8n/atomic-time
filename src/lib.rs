//! Atomic time types
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]

pub use core::sync::atomic::Ordering;

mod duration;
pub use duration::AtomicDuration;
mod option_duration;
pub use option_duration::AtomicOptionDuration;

#[cfg(feature = "std")]
mod system_time;

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use system_time::AtomicSystemTime;

#[cfg(feature = "std")]
mod option_system_time;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use option_system_time::AtomicOptionSystemTime;
