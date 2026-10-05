//! Atomic time types.
//!
//! All types are thread-safe and use `portable_atomic::AtomicU128` under the
//! hood. Operations are lock-free on platforms with native `AtomicU128`
//! support; otherwise, `portable-atomic` may fall back to a global lock. Each
//! type exposes an `is_lock_free` method to query the behavior of the current
//! target.
//!
//! The `std` feature controls the `SystemTime` and `Instant` types. Disable it
//! for `no_std` builds to use the duration types without the standard library.
#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![forbid(unsafe_code)]

pub use core::sync::atomic::Ordering;

use portable_atomic::AtomicU128;

mod duration;
pub use duration::AtomicDuration;
mod option_duration;
pub use option_duration::AtomicOptionDuration;

/// Utility functions for encoding and decoding [`core::time::Duration`] values.
pub mod utils {
  #[cfg(feature = "std")]
  use std::time::{Duration, Instant, SystemTime};

  #[cfg(feature = "std")]
  fn init() -> (Duration, Instant) {
    static ONCE: std::sync::OnceLock<(Duration, Instant)> = std::sync::OnceLock::new();

    *ONCE.get_or_init(|| {
      let epoch_dur = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap();
      let instant_now = Instant::now();
      (epoch_dur, instant_now)
    })
  }

  /// Encodes an [`Instant`] into a [`Duration`] using a process-local baseline.
  ///
  /// The mapping is exact for instants in the same process that are representable
  /// relative to that baseline. The baseline pairs a wall-clock duration with a
  /// monotonic instant once; wall-clock adjustments made afterwards do not change
  /// the mapping. Whether time advances while the machine sleeps inherits the
  /// platform behavior of [`Instant`].
  ///
  /// This encoding is not a durable deadline format. Values decoded in another
  /// process or after a restart are only wall-clock approximations.
  ///
  /// # Panics
  ///
  /// Panics if `instant` cannot be represented as a duration relative to the
  /// process-local baseline.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline(always)]
  pub fn encode_instant_to_duration(instant: Instant) -> Duration {
    let (epoch_dur, instant_now) = init();
    if instant <= instant_now {
      epoch_dur - (instant_now - instant)
    } else {
      epoch_dur + (instant - instant_now)
    }
  }

  /// Decodes an [`Instant`] from a [`Duration`] using the process-local baseline.
  ///
  /// The mapping is exact for values encoded by this process within the platform's
  /// representable `Instant` range. Values outside that range fall back to the
  /// baseline instant; this is a fallback, not saturation. The behavior during
  /// system sleep inherits the platform behavior of [`Instant`]. Encodings from
  /// another process or a previous run are only wall-clock approximations and are
  /// not durable deadlines.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[inline(always)]
  pub fn decode_instant_from_duration(duration: Duration) -> Instant {
    let (epoch_dur, instant_now) = init();
    if duration >= epoch_dur {
      let delta = duration - epoch_dur;
      instant_now.checked_add(delta).unwrap_or(instant_now)
    } else {
      let delta = epoch_dur - duration;
      instant_now.checked_sub(delta).unwrap_or(instant_now)
    }
  }

  pub use super::duration::{decode_duration, encode_duration};
  pub use super::option_duration::{decode_option_duration, encode_option_duration};
}

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
use utils::{decode_instant_from_duration, encode_instant_to_duration};
