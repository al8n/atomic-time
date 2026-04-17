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

/// Utility functions for encoding/decoding [`Duration`] to other types.
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

  /// Encode an [`Instant`] into a [`Duration`].
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn encode_instant_to_duration(instant: Instant) -> Duration {
    let (epoch_dur, instant_now) = init();
    if instant <= instant_now {
      epoch_dur - (instant_now - instant)
    } else {
      epoch_dur + (instant - instant_now)
    }
  }

  /// Decode an [`Instant`] from a [`Duration`].
  ///
  /// Accepts non-canonical input without panicking. If the encoded
  /// Duration is so large that `instant_now + delta` would overflow
  /// `Instant`'s internal representation, the result saturates at
  /// `instant_now` rather than panicking. This is important because
  /// the function sits on the serde deserialization path — a malformed
  /// or adversarial encoded value must not crash the process.
  #[cfg(feature = "std")]
  #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn decode_instant_from_duration(duration: Duration) -> Instant {
    let (epoch_dur, instant_now) = init();
    if duration >= epoch_dur {
      let delta = duration - epoch_dur;
      // `Instant::checked_add` returns `None` when the result
      // would overflow the platform's monotonic-clock range.
      // Fall back to `instant_now` — the decoded Instant is
      // "wrong" for such extreme inputs, but the alternative
      // (panicking) propagates into serde `Deserialize` impls
      // and crashes the caller.
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
