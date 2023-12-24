//! Atomic time types
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs, warnings)]
#![forbid(unsafe_code)]

pub use core::sync::atomic::Ordering;

use portable_atomic::AtomicU128;

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

#[cfg(feature = "std")]
mod instant;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use instant::AtomicInstant;

#[cfg(feature = "std")]
mod option_instant;
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
pub use option_instant::AtomicOptionInstant;

#[cfg(feature = "std")]
use std::{
  sync::OnceLock,
  time::{Duration, Instant, SystemTime},
};

#[cfg(feature = "std")]
fn init(now: Instant) -> (SystemTime, Instant) {
  static ONCE: OnceLock<(SystemTime, Instant)> = OnceLock::new();
  *ONCE.get_or_init(|| {
    let system_now = SystemTime::now();
    (system_now, now)
  })
}

#[cfg(feature = "std")]
#[inline]
fn encode_instant_to_duration(instant: Instant) -> Duration {
  let (system_now, instant_now) = init(instant);
  if instant <= instant_now {
    system_now.duration_since(SystemTime::UNIX_EPOCH).unwrap() + (instant_now - instant)
  } else {
    system_now.duration_since(SystemTime::UNIX_EPOCH).unwrap() + (instant - instant_now)
  }
}

#[cfg(feature = "std")]
#[inline]
fn decode_instant_from_duration(duration: Duration) -> Instant {
  let (system_now, instant_now) = init(Instant::now());
  let system_time = SystemTime::UNIX_EPOCH + duration;
  if system_time >= system_now {
    instant_now + system_time.duration_since(system_now).unwrap()
  } else {
    instant_now - system_now.duration_since(system_time).unwrap()
  }
}
