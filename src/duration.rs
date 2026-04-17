use crate::AtomicU128;
use core::{sync::atomic::Ordering, time::Duration};

/// Atomic version of [`Duration`]
#[repr(transparent)]
pub struct AtomicDuration(AtomicU128);
impl core::fmt::Debug for AtomicDuration {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicDuration")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}
impl Default for AtomicDuration {
  /// Creates an `AtomicDuration` initialized to [`Duration::ZERO`].
  #[inline]
  fn default() -> Self {
    Self::new(Duration::ZERO)
  }
}
impl From<Duration> for AtomicDuration {
  #[inline]
  fn from(duration: Duration) -> Self {
    Self::new(duration)
  }
}
impl AtomicDuration {
  /// Creates a new `AtomicDuration` with the given value.
  #[inline]
  pub const fn new(duration: Duration) -> Self {
    Self(AtomicU128::new(encode_duration(duration)))
  }
  /// Loads [`Duration`](Duration) from `AtomicDuration`.
  ///
  /// load takes an [`Ordering`] argument which describes the memory ordering of this operation.
  ///
  /// # Panics
  /// Panics if order is [`Release`](Ordering::Release) or [`AcqRel`](Ordering::AcqRel).
  #[inline]
  pub fn load(&self, ordering: Ordering) -> Duration {
    decode_duration(self.0.load(ordering))
  }
  /// Stores a value into the `AtomicDuration`.
  ///
  /// `store` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  ///
  /// # Panics
  ///
  /// Panics if `order` is [`Acquire`](Ordering::Acquire) or [`AcqRel`](Ordering::AcqRel).
  #[inline]
  pub fn store(&self, val: Duration, ordering: Ordering) {
    self.0.store(encode_duration(val), ordering)
  }
  /// Stores a value into the `AtomicDuration`, returning the old value.
  ///
  /// `swap` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  #[inline]
  pub fn swap(&self, val: Duration, ordering: Ordering) -> Duration {
    decode_duration(self.0.swap(encode_duration(val), ordering))
  }
  /// Stores a value into the `AtomicDuration` if the current value is the same as the
  /// `current` value.
  ///
  /// Unlike [`compare_exchange`], this function is allowed to spuriously fail
  /// even when the comparison succeeds, which can result in more efficient
  /// code on some platforms. The return value is a result indicating whether
  /// the new value was written and containing the previous value.
  ///
  /// `compare_exchange` takes two [`Ordering`] arguments to describe the memory
  /// ordering of this operation. The first describes the required ordering if
  /// the operation succeeds while the second describes the required ordering
  /// when the operation fails. The failure ordering can't be [`Release`](Ordering::Release) or
  /// [`AcqRel`](Ordering::AcqRel) and must be equivalent or weaker than the success ordering.
  /// success ordering.
  ///
  /// [`compare_exchange`]: #method.compare_exchange
  #[inline]
  pub fn compare_exchange_weak(
    &self,
    current: Duration,
    new: Duration,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Duration, Duration> {
    self
      .0
      .compare_exchange_weak(
        encode_duration(current),
        encode_duration(new),
        success,
        failure,
      )
      .map(decode_duration)
      .map_err(decode_duration)
  }
  /// Stores a value into the `AtomicDuration` if the current value is the same as the
  /// `current` value.
  ///
  /// The return value is a result indicating whether the new value was
  /// written and containing the previous value. On success this value is
  /// guaranteed to be equal to `new`.
  ///
  /// [`compare_exchange`] takes two [`Ordering`] arguments to describe the memory
  /// ordering of this operation. The first describes the required ordering if
  /// the operation succeeds while the second describes the required ordering
  /// when the operation fails. The failure ordering can't be [`Release`](Ordering::Release) or
  /// [`AcqRel`](Ordering::AcqRel) and must be equivalent or weaker than the success ordering.
  ///
  /// [`compare_exchange`]: #method.compare_exchange
  #[inline]
  pub fn compare_exchange(
    &self,
    current: Duration,
    new: Duration,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Duration, Duration> {
    self
      .0
      .compare_exchange(
        encode_duration(current),
        encode_duration(new),
        success,
        failure,
      )
      .map(decode_duration)
      .map_err(decode_duration)
  }
  /// Fetches the value, and applies a function to it that returns an optional
  /// new value. Returns a `Result` of `Ok(previous_value)` if the function returned `Some(_)`, else
  /// `Err(previous_value)`.
  ///
  /// Note: This may call the function multiple times if the value has been changed from other threads in
  /// the meantime, as long as the function returns `Some(_)`, but the function will have been applied
  /// only once to the stored value.
  ///
  /// `fetch_update` takes two [`Ordering`] arguments to describe the memory ordering of this operation.
  /// The first describes the required ordering for when the operation finally succeeds while the second
  /// describes the required ordering for loads. These correspond to the success and failure orderings of
  /// [`compare_exchange`] respectively.
  ///
  /// Using [`Acquire`](Ordering::Acquire) as success ordering makes the store part
  /// of this operation [`Relaxed`](Ordering::Relaxed), and using [`Release`](Ordering::Release) makes the final successful load
  /// [`Relaxed`](Ordering::Relaxed). The (failed) load ordering can only be [`SeqCst`](Ordering::SeqCst), [`Acquire`](Ordering::Acquire) or [`Relaxed`](Ordering::Release)
  /// and must be equivalent to or weaker than the success ordering.
  ///
  /// [`compare_exchange`]: #method.compare_exchange
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicDuration;
  /// use std::{time::Duration, sync::atomic::Ordering};
  ///
  /// let x = AtomicDuration::new(Duration::from_secs(7));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(Duration::from_secs(7)));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x + Duration::from_secs(1))), Ok(Duration::from_secs(7)));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x + Duration::from_secs(1))), Ok(Duration::from_secs(8)));
  /// assert_eq!(x.load(Ordering::SeqCst), Duration::from_secs(9));
  /// ```
  #[inline]
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<Duration, Duration>
  where
    F: FnMut(Duration) -> Option<Duration>,
  {
    self
      .0
      .fetch_update(set_order, fetch_order, |d| {
        f(decode_duration(d)).map(encode_duration)
      })
      .map(decode_duration)
      .map_err(decode_duration)
  }
  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[inline]
  pub fn into_inner(self) -> Duration {
    decode_duration(self.0.into_inner())
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicDuration;
  ///
  /// let is_lock_free = AtomicDuration::is_lock_free();
  /// ```
  #[inline]
  pub fn is_lock_free() -> bool {
    AtomicU128::is_lock_free()
  }
}

/// Encodes a [`Duration`] into a [`u128`].
#[inline]
pub const fn encode_duration(duration: Duration) -> u128 {
  let seconds = duration.as_secs() as u128;
  let nanos = duration.subsec_nanos() as u128;
  (seconds << 32) + nanos
}

/// Decodes a [`u128`] into a [`Duration`].
///
/// Accepts non-canonical input without panicking. The encoding
/// produced by [`encode_duration`] stores 64 bits of seconds in bits
/// 32..=95 and at most 30 bits of nanoseconds (the valid range
/// `0..1_000_000_000`) in bits 0..=31. If the decoded bits carry a
/// nanosecond count of 10⁹ or more — which `encode_duration` never
/// produces, but which can appear when the encoded value comes from
/// corrupted storage or untrusted input — the extra whole seconds are
/// folded into the seconds field; if that push past `u64::MAX`, the
/// result saturates at [`Duration::MAX`].
///
/// This means `decode_duration(u128::MAX)` yields a saturated
/// `Duration` rather than panicking as the previous implementation
/// did.
#[inline]
pub const fn decode_duration(encoded: u128) -> Duration {
  let seconds = (encoded >> 32) as u64;
  let raw_nanos = (encoded & 0xFFFFFFFF) as u32;
  // Normalize out-of-range nanoseconds before calling `Duration::new`
  // — the latter panics if the carry from nanos overflows the
  // seconds field.
  let extra_secs = (raw_nanos / 1_000_000_000) as u64;
  let nanos = raw_nanos % 1_000_000_000;
  match seconds.checked_add(extra_secs) {
    Some(secs) => Duration::new(secs, nanos),
    None => Duration::new(u64::MAX, 999_999_999),
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicDuration {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicDuration {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(Duration::deserialize(deserializer)?))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_atomic_duration_new() {
    let duration = Duration::from_secs(5);
    let atomic_duration = AtomicDuration::new(duration);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), duration);
  }

  #[test]
  fn test_atomic_duration_load() {
    let duration = Duration::new(10, 10);
    let atomic_duration = AtomicDuration::new(duration);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), duration);
  }

  #[test]
  fn test_atomic_duration_store() {
    let initial_duration = Duration::from_secs(3);
    let new_duration = Duration::from_secs(7);
    let atomic_duration = AtomicDuration::new(initial_duration);
    atomic_duration.store(new_duration, Ordering::SeqCst);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), new_duration);
  }

  #[test]
  fn test_atomic_duration_swap() {
    let initial_duration = Duration::from_secs(2);
    let new_duration = Duration::from_secs(8);
    let atomic_duration = AtomicDuration::new(initial_duration);
    let prev_duration = atomic_duration.swap(new_duration, Ordering::SeqCst);
    assert_eq!(prev_duration, initial_duration);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), new_duration);
  }

  #[test]
  fn test_atomic_duration_compare_exchange_weak() {
    let initial_duration = Duration::from_secs(4);
    let atomic_duration = AtomicDuration::new(initial_duration);

    // Successful exchange
    let mut result;
    loop {
      result = atomic_duration.compare_exchange_weak(
        initial_duration,
        Duration::from_secs(6),
        Ordering::SeqCst,
        Ordering::SeqCst,
      );

      if result.is_ok() || result.unwrap_err() != initial_duration {
        // Break if successfully updated or if the current value is no longer initial_duration.
        break;
      }
    }

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), initial_duration);
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Duration::from_secs(6)
    );

    // Failed exchange
    // Here, we expect this to fail as the current value is no longer `initial_duration`.
    let result = atomic_duration.compare_exchange_weak(
      initial_duration,
      Duration::from_secs(7),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );

    assert!(result.is_err());
    // The error should be the current value, which is now Duration::from_secs(6).
    assert_eq!(result.unwrap_err(), Duration::from_secs(6));
  }

  #[test]
  fn test_atomic_duration_compare_exchange() {
    let initial_duration = Duration::from_secs(1);
    let atomic_duration = AtomicDuration::new(initial_duration);

    // Successful exchange
    let result = atomic_duration.compare_exchange(
      initial_duration,
      Duration::from_secs(5),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), initial_duration);
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Duration::from_secs(5)
    );

    // Failed exchange
    let result = atomic_duration.compare_exchange(
      initial_duration,
      Duration::from_secs(6),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), Duration::from_secs(5));
  }

  #[test]
  fn test_atomic_duration_fetch_update() {
    let initial_duration = Duration::from_secs(4);
    let atomic_duration = AtomicDuration::new(initial_duration);

    let result = atomic_duration.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |d| {
      Some(d + Duration::from_secs(2))
    });
    assert_eq!(result, Ok(initial_duration));
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Duration::from_secs(6)
    );
  }

  #[test]
  fn test_atomic_duration_into_inner() {
    let duration = Duration::from_secs(3);
    let atomic_duration = AtomicDuration::new(duration);
    assert_eq!(atomic_duration.into_inner(), duration);
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_atomic_duration_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    let atomic_duration = Arc::new(AtomicDuration::new(Duration::from_secs(0)));
    let mut handles = vec![];

    // Spawn multiple threads to increment the duration
    for _ in 0..10 {
      let atomic_clone = Arc::clone(&atomic_duration);
      let handle = thread::spawn(move || {
        for _ in 0..100 {
          loop {
            let current = atomic_clone.load(Ordering::SeqCst);
            let new = current + Duration::from_millis(1);
            match atomic_clone.compare_exchange_weak(
              current,
              new,
              Ordering::SeqCst,
              Ordering::SeqCst,
            ) {
              Ok(_) => break,     // Successfully updated
              Err(_) => continue, // Spurious failure, try again
            }
          }
        }
      });
      handles.push(handle);
    }

    // Wait for all threads to complete
    for handle in handles {
      handle.join().unwrap();
    }

    // Verify the final value
    let expected_duration = Duration::from_millis(10 * 100);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), expected_duration);
  }

  #[cfg(feature = "std")]
  #[test]
  fn test_atomic_duration_debug() {
    let duration = Duration::new(1, 500_000_000);
    let atomic_duration = AtomicDuration::new(duration);
    let debug_str = format!("{:?}", atomic_duration);
    assert!(debug_str.contains("AtomicDuration"));
  }

  #[test]
  fn test_atomic_duration_default() {
    let atomic_duration = AtomicDuration::default();
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Duration::ZERO);
  }

  #[test]
  fn test_atomic_duration_from() {
    let duration = Duration::from_secs(42);
    let atomic_duration = AtomicDuration::from(duration);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), duration);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_duration_serde() {
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize)]
    struct Test {
      duration: AtomicDuration,
    }

    let test = Test {
      duration: AtomicDuration::new(Duration::from_secs(5)),
    };
    let serialized = serde_json::to_string(&test).unwrap();
    let deserialized: Test = serde_json::from_str(&serialized).unwrap();
    assert_eq!(
      deserialized.duration.load(Ordering::SeqCst),
      Duration::from_secs(5)
    );
  }

  #[test]
  fn decode_duration_roundtrip() {
    let cases = [
      Duration::ZERO,
      Duration::from_secs(1),
      Duration::new(123_456_789, 999_999_999),
      Duration::new(u64::MAX, 999_999_999),
    ];
    for d in cases {
      assert_eq!(decode_duration(encode_duration(d)), d);
    }
  }

  #[test]
  fn decode_duration_saturates_on_non_canonical_input() {
    // u128::MAX has nanos = u32::MAX (> 1e9) and seconds = u64::MAX,
    // so the carry from normalising nanos overflows u64 — the old
    // implementation panicked here.
    let max = decode_duration(u128::MAX);
    assert_eq!(max, Duration::new(u64::MAX, 999_999_999));

    // A value with just out-of-range nanos (but within seconds budget):
    // encode(0 secs, 2_000_000_000 nanos) — hand-crafted, not produced
    // by encode_duration.
    let d = decode_duration(2_000_000_000u128);
    assert_eq!(d, Duration::new(2, 0));
  }
}
