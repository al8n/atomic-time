use crate::AtomicU128;
use core::{sync::atomic::Ordering, time::Duration};

/// Atomic version of [`Option<Duration>`].
#[repr(transparent)]
pub struct AtomicOptionDuration(AtomicU128);
impl core::fmt::Debug for AtomicOptionDuration {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicOptionDuration")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}
impl Default for AtomicOptionDuration {
  /// Creates an `AtomicOptionDuration` initialized to `None`.
  #[inline(always)]
  fn default() -> Self {
    Self::none()
  }
}
impl From<Option<Duration>> for AtomicOptionDuration {
  #[inline(always)]
  fn from(duration: Option<Duration>) -> Self {
    Self::new(duration)
  }
}
impl AtomicOptionDuration {
  /// Creates a new `AtomicOptionDuration` with `None`.
  #[inline(always)]
  pub const fn none() -> Self {
    Self(AtomicU128::new(encode_option_duration(None)))
  }

  /// Creates a new `AtomicOptionDuration` with the given value.
  #[inline(always)]
  pub const fn new(duration: Option<Duration>) -> Self {
    Self(AtomicU128::new(encode_option_duration(duration)))
  }
  /// Loads `Option<Duration>` from `AtomicOptionDuration`.
  ///
  /// load takes an [`Ordering`] argument which describes the memory ordering of this operation.
  ///
  /// # Panics
  /// Panics if order is [`Release`](Ordering::Release) or [`AcqRel`](Ordering::AcqRel).
  #[inline(always)]
  pub fn load(&self, ordering: Ordering) -> Option<Duration> {
    decode_option_duration(self.0.load(ordering))
  }
  /// Stores a value into the `AtomicOptionDuration`.
  ///
  /// `store` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  ///
  /// # Panics
  ///
  /// Panics if `order` is [`Acquire`](Ordering::Acquire) or [`AcqRel`](Ordering::AcqRel).
  #[inline(always)]
  pub fn store(&self, val: Option<Duration>, ordering: Ordering) {
    self.0.store(encode_option_duration(val), ordering)
  }
  /// Stores a value into the `AtomicOptionDuration`, returning the old value.
  ///
  /// `swap` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  #[inline(always)]
  pub fn swap(&self, val: Option<Duration>, ordering: Ordering) -> Option<Duration> {
    decode_option_duration(self.0.swap(encode_option_duration(val), ordering))
  }
  /// Stores a value into the `AtomicOptionDuration` if the current value is the same as the
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
  #[inline(always)]
  pub fn compare_exchange_weak(
    &self,
    current: Option<Duration>,
    new: Option<Duration>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<Duration>, Option<Duration>> {
    self
      .0
      .compare_exchange_weak(
        encode_option_duration(current),
        encode_option_duration(new),
        success,
        failure,
      )
      .map(decode_option_duration)
      .map_err(decode_option_duration)
  }
  /// Stores a value into the `AtomicOptionDuration` if the current value is the same as the
  /// `current` value.
  ///
  /// The return value is a result indicating whether the new value was
  /// written and containing the previous value. On success this value is
  /// guaranteed to be equal to `current`.
  ///
  /// [`compare_exchange`] takes two [`Ordering`] arguments to describe the memory
  /// ordering of this operation. The first describes the required ordering if
  /// the operation succeeds while the second describes the required ordering
  /// when the operation fails. The failure ordering can't be [`Release`](Ordering::Release) or
  /// [`AcqRel`](Ordering::AcqRel) and must be equivalent or weaker than the success ordering.
  ///
  /// [`compare_exchange`]: #method.compare_exchange
  #[inline(always)]
  pub fn compare_exchange(
    &self,
    current: Option<Duration>,
    new: Option<Duration>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<Duration>, Option<Duration>> {
    self
      .0
      .compare_exchange(
        encode_option_duration(current),
        encode_option_duration(new),
        success,
        failure,
      )
      .map(decode_option_duration)
      .map_err(decode_option_duration)
  }
  /// Fetches the value and applies a function that can choose whether to store
  /// a new value.
  ///
  /// Returns `Ok(previous_value)` when `f` returns `Some(_)`, and
  /// `Err(previous_value)` when it returns `None`. The outer `Option` is the
  /// update decision; returning `Some(None)` stores `None`. The closure can run
  /// more than once when another thread changes the value concurrently, but it
  /// is applied only once to the value that is stored.
  ///
  /// `set_order` describes the ordering of the successful update and
  /// `fetch_order` describes failed compare-and-exchange loads. They have the
  /// same requirements as the success and failure orderings of
  /// [`compare_exchange`](Self::compare_exchange).
  ///
  /// # Panics
  ///
  /// Panics if the orderings are invalid for
  /// [`compare_exchange`](Self::compare_exchange).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::new(Some(Duration::from_secs(7)));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(Some(Duration::from_secs(7))));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| Some(None)), Ok(Some(Duration::from_secs(7))));
  /// ```
  #[inline(always)]
  pub fn try_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<Option<Duration>, Option<Duration>>
  where
    F: FnMut(Option<Duration>) -> Option<Option<Duration>>,
  {
    self
      .0
      .fetch_update(set_order, fetch_order, |d| {
        f(decode_option_duration(d)).map(encode_option_duration)
      })
      .map(decode_option_duration)
      .map_err(decode_option_duration)
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
  /// [`Relaxed`](Ordering::Relaxed). The (failed) load ordering can only be [`SeqCst`](Ordering::SeqCst), [`Acquire`](Ordering::Acquire) or [`Relaxed`](Ordering::Relaxed)
  /// and must be equivalent to or weaker than the success ordering.
  ///
  /// [`compare_exchange`]: #method.compare_exchange
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{time::Duration, sync::atomic::Ordering};
  ///
  /// let x = AtomicOptionDuration::new(Some(Duration::from_secs(7)));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(Some(Duration::from_secs(7))));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(Duration::from_secs(7))));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(Duration::from_secs(8))));
  /// assert_eq!(x.load(Ordering::SeqCst), Some(Duration::from_secs(9)));
  /// ```
  #[inline(always)]
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    f: F,
  ) -> Result<Option<Duration>, Option<Duration>>
  where
    F: FnMut(Option<Duration>) -> Option<Option<Duration>>,
  {
    self.try_update(set_order, fetch_order, f)
  }

  /// Fetches the value, applies a function to produce a new value, stores it,
  /// and returns the previous value.
  ///
  /// The closure can run more than once when another thread changes the value
  /// concurrently, but it is applied only once to the value that is stored.
  /// `set_order` and `fetch_order` have the same requirements as the success
  /// and failure orderings of [`compare_exchange`](Self::compare_exchange).
  ///
  /// # Panics
  ///
  /// Panics if the orderings are invalid for
  /// [`compare_exchange`](Self::compare_exchange).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::new(Some(Duration::from_secs(7)));
  /// assert_eq!(x.update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Some(Duration::from_secs(7)));
  /// assert_eq!(x.load(Ordering::SeqCst), None);
  /// ```
  #[inline(always)]
  pub fn update<F>(&self, set_order: Ordering, fetch_order: Ordering, mut f: F) -> Option<Duration>
  where
    F: FnMut(Option<Duration>) -> Option<Duration>,
  {
    let mut current = self.0.load(fetch_order);
    loop {
      let new = encode_option_duration(f(decode_option_duration(current)));
      match self
        .0
        .compare_exchange_weak(current, new, set_order, fetch_order)
      {
        Ok(previous) => return decode_option_duration(previous),
        Err(actual) => current = actual,
      }
    }
  }

  /// Atomically stores the smaller of the current value and `val`, returning
  /// the previous value.
  ///
  /// The encoded ordering is `None < Some(duration)`, and `Some` values use
  /// their natural [`Duration`] ordering. `order` describes the memory ordering
  /// of the read-modify-write operation.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::new(Some(Duration::from_secs(7)));
  /// assert_eq!(x.fetch_min(None, Ordering::SeqCst), Some(Duration::from_secs(7)));
  /// assert_eq!(x.load(Ordering::SeqCst), None);
  /// ```
  #[inline(always)]
  pub fn fetch_min(&self, val: Option<Duration>, order: Ordering) -> Option<Duration> {
    decode_option_duration(self.0.fetch_min(encode_option_duration(val), order))
  }

  /// Atomically stores the larger of the current value and `val`, returning
  /// the previous value.
  ///
  /// The encoded ordering is `None < Some(duration)`, and `Some` values use
  /// their natural [`Duration`] ordering. `order` describes the memory ordering
  /// of the read-modify-write operation.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::new(None);
  /// assert_eq!(x.fetch_max(Some(Duration::from_secs(7)), Ordering::SeqCst), None);
  /// assert_eq!(x.load(Ordering::SeqCst), Some(Duration::from_secs(7)));
  /// ```
  #[inline(always)]
  pub fn fetch_max(&self, val: Option<Duration>, order: Ordering) -> Option<Duration> {
    decode_option_duration(self.0.fetch_max(encode_option_duration(val), order))
  }

  /// Adds `val` to a contained duration with saturation, returning the previous
  /// value.
  ///
  /// `Some(duration)` is replaced with `Some(duration.saturating_add(val))`.
  /// `None` remains `None`; it is never treated as [`Duration::ZERO`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::none();
  /// assert_eq!(x.fetch_saturating_add(Duration::from_nanos(1), Ordering::SeqCst), None);
  /// assert_eq!(x.load(Ordering::SeqCst), None);
  /// ```
  #[inline(always)]
  pub fn fetch_saturating_add(&self, val: Duration, order: Ordering) -> Option<Duration> {
    self.update(order, Ordering::Relaxed, |old| {
      old.map(|duration| duration.saturating_add(val))
    })
  }

  /// Subtracts `val` from a contained duration with saturation, returning the
  /// previous value.
  ///
  /// `Some(duration)` is replaced with `Some(duration.saturating_sub(val))`.
  /// `None` remains `None`; it is never treated as [`Duration::ZERO`].
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  /// use std::{sync::atomic::Ordering, time::Duration};
  ///
  /// let x = AtomicOptionDuration::none();
  /// assert_eq!(x.fetch_saturating_sub(Duration::from_nanos(1), Ordering::SeqCst), None);
  /// assert_eq!(x.load(Ordering::SeqCst), None);
  /// ```
  #[inline(always)]
  pub fn fetch_saturating_sub(&self, val: Duration, order: Ordering) -> Option<Duration> {
    self.update(order, Ordering::Relaxed, |old| {
      old.map(|duration| duration.saturating_sub(val))
    })
  }
  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[inline(always)]
  pub fn into_inner(self) -> Option<Duration> {
    decode_option_duration(self.0.into_inner())
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicOptionDuration;
  ///
  /// let is_lock_free = AtomicOptionDuration::is_lock_free();
  /// ```
  #[inline(always)]
  pub fn is_lock_free() -> bool {
    AtomicU128::is_lock_free()
  }

  /// Returns whether operations on values of this type are always lock-free.
  ///
  /// A `false` result does not preclude lock-free operations selected through
  /// runtime CPU feature detection; use [`is_lock_free`](Self::is_lock_free)
  /// to query the current target at runtime.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionDuration;
  ///
  /// const ALWAYS_LOCK_FREE: bool = AtomicOptionDuration::is_always_lock_free();
  /// let _ = ALWAYS_LOCK_FREE;
  /// ```
  #[inline(always)]
  pub const fn is_always_lock_free() -> bool {
    AtomicU128::is_always_lock_free()
  }
}

/// Encode an [`Option<Duration>`] into an [`u128`].
#[inline(always)]
pub const fn encode_option_duration(option_duration: Option<Duration>) -> u128 {
  match option_duration {
    Some(duration) => {
      let seconds = duration.as_secs() as u128;
      let nanos = duration.subsec_nanos() as u128;
      (1 << 127) | (seconds << 32) | nanos
    }
    None => 0,
  }
}

/// Decode an [`Option<Duration>`] from an encoded [`u128`].
///
/// Accepts non-canonical input without panicking. The `Some(_)`
/// encoding stores 64 bits of seconds in bits 32..=95 and up to 30
/// bits of nanoseconds in bits 0..=31 (bit 127 is the Some/None
/// discriminant, bits 96..=126 are unused). If the decoded nanosecond
/// count is 10⁹ or more — which `encode_option_duration` never
/// produces, but which can appear when the encoded value comes from
/// corrupted storage or untrusted input — the extra whole seconds are
/// folded into the seconds field; if that push past `u64::MAX`, the
/// result saturates at [`Duration::MAX`].
///
/// This means `decode_option_duration(u128::MAX)` yields
/// `Some(Duration::MAX)` rather than panicking as the previous
/// implementation did.
#[inline(always)]
pub const fn decode_option_duration(encoded: u128) -> Option<Duration> {
  if encoded >> 127 == 0 {
    None
  } else {
    let seconds = ((encoded << 1) >> 33) as u64;
    let raw_nanos = (encoded & 0xFFFFFFFF) as u32;
    let extra_secs = (raw_nanos / 1_000_000_000) as u64;
    let nanos = raw_nanos % 1_000_000_000;
    Some(match seconds.checked_add(extra_secs) {
      Some(secs) => Duration::new(secs, nanos),
      None => Duration::new(u64::MAX, 999_999_999),
    })
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicOptionDuration {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicOptionDuration {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(Option::<Duration>::deserialize(deserializer)?))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_new_atomic_option_duration() {
    let duration = Duration::from_secs(5);
    let atomic_duration = AtomicOptionDuration::new(Some(duration));
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(duration));
  }

  #[test]
  fn test_atomic_option_duration_load() {
    let duration = Duration::from_secs(10);
    let atomic_duration = AtomicOptionDuration::new(Some(duration));
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(duration));
  }

  #[test]
  fn test_atomic_option_duration_store() {
    let initial_duration = Duration::from_secs(3);
    let new_duration = Duration::from_secs(7);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));
    atomic_duration.store(Some(new_duration), Ordering::SeqCst);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(new_duration));
  }

  #[test]
  fn test_atomic_option_duration_store_none() {
    let initial_duration = Duration::from_secs(3);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));
    atomic_duration.store(None, Ordering::SeqCst);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_swap() {
    let initial_duration = Duration::from_secs(2);
    let new_duration = Duration::from_secs(8);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));
    let prev_duration = atomic_duration.swap(Some(new_duration), Ordering::SeqCst);
    assert_eq!(prev_duration, Some(initial_duration));
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(new_duration));
  }

  #[test]
  fn test_atomic_option_duration_compare_exchange_weak() {
    let initial_duration = Duration::from_secs(4);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));

    // Successful exchange
    let mut result;
    loop {
      result = atomic_duration.compare_exchange_weak(
        Some(initial_duration),
        Some(Duration::from_secs(6)),
        Ordering::SeqCst,
        Ordering::SeqCst,
      );

      if result.is_ok() {
        break;
      }
    }

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Some(initial_duration));
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_secs(6))
    );

    // Failed exchange
    let result = atomic_duration.compare_exchange_weak(
      Some(initial_duration),
      Some(Duration::from_secs(7)),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), Some(Duration::from_secs(6)));
  }

  #[test]
  fn test_atomic_option_duration_compare_exchange() {
    let initial_duration = Duration::from_secs(1);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));

    // Successful exchange
    let result = atomic_duration.compare_exchange(
      Some(initial_duration),
      Some(Duration::from_secs(5)),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Some(initial_duration));
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_secs(5))
    );

    // Failed exchange
    let result = atomic_duration.compare_exchange(
      Some(initial_duration),
      Some(Duration::from_secs(6)),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), Some(Duration::from_secs(5)));
  }

  #[test]
  fn test_atomic_option_duration_with_none_initially() {
    let atomic_duration = AtomicOptionDuration::new(None);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_store_none_and_then_value() {
    let atomic_duration = AtomicOptionDuration::new(None);
    atomic_duration.store(Some(Duration::from_secs(5)), Ordering::SeqCst);
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_secs(5))
    );
  }

  #[test]
  fn test_atomic_option_duration_swap_with_none() {
    let initial_duration = Duration::from_secs(2);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));
    let prev_duration = atomic_duration.swap(None, Ordering::SeqCst);
    assert_eq!(prev_duration, Some(initial_duration));
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_compare_exchange_weak_with_none() {
    let initial_duration = Duration::from_secs(4);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));

    // Change to None
    let mut result;

    loop {
      result = atomic_duration.compare_exchange_weak(
        Some(initial_duration),
        None,
        Ordering::SeqCst,
        Ordering::SeqCst,
      );

      if result.is_ok() {
        break;
      }
    }

    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);

    // Change back to Some(Duration)
    let new_duration = Duration::from_secs(6);
    let mut result;

    loop {
      result = atomic_duration.compare_exchange_weak(
        None,
        Some(new_duration),
        Ordering::SeqCst,
        Ordering::SeqCst,
      );
      if result.is_ok() {
        break;
      }
    }

    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(new_duration));
  }

  #[test]
  fn test_atomic_option_duration_compare_exchange_with_none() {
    let initial_duration = Duration::from_secs(1);
    let atomic_duration = AtomicOptionDuration::new(Some(initial_duration));

    // Change to None
    let result = atomic_duration.compare_exchange(
      Some(initial_duration),
      None,
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_ok());
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);

    // Change back to Some(Duration)
    let new_duration = Duration::from_secs(5);
    let result = atomic_duration.compare_exchange(
      None,
      Some(new_duration),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_ok());
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(new_duration));
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_atomic_option_duration_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    let atomic_duration = Arc::new(AtomicOptionDuration::new(Some(Duration::from_secs(0))));
    let mut handles = vec![];

    // Spawn multiple threads to increment the duration
    for _ in 0..10 {
      let atomic_clone = Arc::clone(&atomic_duration);
      let handle = thread::spawn(move || {
        for _ in 0..100 {
          loop {
            let current = atomic_clone.load(Ordering::SeqCst);
            let new_duration = current
              .map(|d| d + Duration::from_millis(1))
              .or(Some(Duration::from_millis(1)));
            match atomic_clone.compare_exchange_weak(
              current,
              new_duration,
              Ordering::SeqCst,
              Ordering::SeqCst,
            ) {
              Ok(_) => break,     // Successfully updated
              Err(_) => continue, // Spurious failure, retry
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
    let expected_duration = Some(Duration::from_millis(10 * 100));
    assert_eq!(atomic_duration.load(Ordering::SeqCst), expected_duration);
  }

  #[cfg(feature = "std")]
  #[test]
  fn test_atomic_option_duration_debug() {
    let atomic_duration = AtomicOptionDuration::new(Some(Duration::from_secs(1)));
    let debug_str = format!("{:?}", atomic_duration);
    assert!(debug_str.contains("AtomicOptionDuration"));
  }

  #[cfg(feature = "std")]
  #[test]
  fn test_atomic_option_duration_debug_none() {
    let atomic_duration = AtomicOptionDuration::none();
    let debug_str = format!("{:?}", atomic_duration);
    assert!(debug_str.contains("AtomicOptionDuration"));
  }

  #[test]
  fn test_atomic_option_duration_default() {
    let atomic_duration = AtomicOptionDuration::default();
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_from() {
    let duration = Some(Duration::from_secs(42));
    let atomic_duration = AtomicOptionDuration::from(duration);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), duration);
  }

  #[test]
  fn test_atomic_option_duration_from_none() {
    let atomic_duration = AtomicOptionDuration::from(None);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_into_inner() {
    let duration = Some(Duration::from_secs(3));
    let atomic_duration = AtomicOptionDuration::new(duration);
    assert_eq!(atomic_duration.into_inner(), duration);
  }

  #[test]
  fn test_atomic_option_duration_into_inner_none() {
    let atomic_duration = AtomicOptionDuration::none();
    assert_eq!(atomic_duration.into_inner(), None);
  }

  #[test]
  fn test_atomic_option_duration_fetch_update() {
    let initial = Some(Duration::from_secs(4));
    let atomic_duration = AtomicOptionDuration::new(initial);

    let result = atomic_duration.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |d| {
      Some(d.map(|val| val + Duration::from_secs(2)))
    });
    assert_eq!(result, Ok(initial));
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_secs(6))
    );

    // fetch_update returning None should fail
    let result = atomic_duration.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None);
    assert!(result.is_err());
  }

  #[test]
  fn test_atomic_option_duration_try_update() {
    let initial = Some(Duration::from_secs(4));
    let atomic_duration = AtomicOptionDuration::new(initial);

    assert_eq!(
      atomic_duration.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None),
      Err(initial)
    );
    assert_eq!(
      atomic_duration.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| Some(None)),
      Ok(initial)
    );
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_update_returns_previous_value() {
    let initial = Some(Duration::from_secs(4));
    let atomic_duration = AtomicOptionDuration::new(initial);

    assert_eq!(
      atomic_duration.update(Ordering::SeqCst, Ordering::SeqCst, |_| None),
      initial
    );
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_duration_fetch_min_and_max() {
    let low = Some(Duration::from_secs(3));
    let middle = Some(Duration::from_secs(5));
    let high = Some(Duration::from_secs(7));
    let atomic_duration = AtomicOptionDuration::new(middle);

    assert_eq!(atomic_duration.fetch_min(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.fetch_min(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.fetch_min(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), low);

    atomic_duration.store(middle, Ordering::SeqCst);
    assert_eq!(atomic_duration.fetch_max(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.fetch_max(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.fetch_max(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), high);

    atomic_duration.store(None, Ordering::SeqCst);
    assert_eq!(atomic_duration.fetch_min(low, Ordering::SeqCst), None);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), None);
    assert_eq!(atomic_duration.fetch_max(low, Ordering::SeqCst), None);
    assert_eq!(atomic_duration.load(Ordering::SeqCst), low);
  }

  #[test]
  fn test_atomic_option_duration_fetch_saturating_arithmetic() {
    let none = AtomicOptionDuration::none();
    assert_eq!(
      none.fetch_saturating_add(Duration::from_nanos(1), Ordering::SeqCst),
      None
    );
    assert_eq!(none.load(Ordering::SeqCst), None);
    assert_eq!(
      none.fetch_saturating_sub(Duration::from_nanos(1), Ordering::SeqCst),
      None
    );
    assert_eq!(none.load(Ordering::SeqCst), None);

    let atomic_duration = AtomicOptionDuration::new(Some(Duration::new(0, 999_999_999)));
    assert_eq!(
      atomic_duration.fetch_saturating_add(Duration::from_nanos(1), Ordering::SeqCst),
      Some(Duration::new(0, 999_999_999))
    );
    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_secs(1))
    );

    atomic_duration.store(Some(Duration::MAX), Ordering::SeqCst);
    assert_eq!(
      atomic_duration.fetch_saturating_add(Duration::from_nanos(1), Ordering::SeqCst),
      Some(Duration::MAX)
    );
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(Duration::MAX));

    atomic_duration.store(Some(Duration::ZERO), Ordering::SeqCst);
    assert_eq!(
      atomic_duration.fetch_saturating_sub(Duration::from_nanos(1), Ordering::SeqCst),
      Some(Duration::ZERO)
    );
    assert_eq!(atomic_duration.load(Ordering::SeqCst), Some(Duration::ZERO));
  }

  #[test]
  fn test_atomic_option_duration_always_lock_free_implies_lock_free() {
    assert!(!AtomicOptionDuration::is_always_lock_free() || AtomicOptionDuration::is_lock_free());
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_atomic_option_duration_saturating_add_is_exact_under_contention() {
    use std::sync::Arc;
    use std::thread;

    let atomic_duration = Arc::new(AtomicOptionDuration::new(Some(Duration::ZERO)));
    let mut handles = vec![];

    for _ in 0..4 {
      let atomic_clone = Arc::clone(&atomic_duration);
      handles.push(thread::spawn(move || {
        for _ in 0..100 {
          atomic_clone.fetch_saturating_add(Duration::from_nanos(1), Ordering::SeqCst);
        }
      }));
    }

    for handle in handles {
      handle.join().unwrap();
    }

    assert_eq!(
      atomic_duration.load(Ordering::SeqCst),
      Some(Duration::from_nanos(400))
    );
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_option_duration_serde() {
    for duration in [Some(Duration::from_secs(5)), None] {
      let atomic = AtomicOptionDuration::new(duration);
      let serialized = serde_json::to_string(&atomic).unwrap();
      let deserialized: AtomicOptionDuration = serde_json::from_str(&serialized).unwrap();
      assert_eq!(deserialized.load(Ordering::SeqCst), duration);
    }
  }

  #[test]
  fn decode_option_duration_roundtrip() {
    let cases: [Option<Duration>; 4] = [
      None,
      Some(Duration::ZERO),
      Some(Duration::from_secs(1)),
      Some(Duration::new(123_456_789, 999_999_999)),
    ];
    for d in cases {
      assert_eq!(decode_option_duration(encode_option_duration(d)), d);
    }
  }

  #[test]
  fn decode_option_duration_saturates_on_non_canonical_input() {
    // u128::MAX has bit 127 set (= Some), nanos = u32::MAX (> 1e9),
    // and the extracted seconds = u64::MAX. The old implementation
    // panicked; the new one saturates.
    let max = decode_option_duration(u128::MAX);
    assert_eq!(max, Some(Duration::new(u64::MAX, 999_999_999)));

    // Zero is the None sentinel — verify it stays None even when all
    // lower bits are clear.
    assert_eq!(decode_option_duration(0), None);

    // Bit 127 alone = Some with seconds=0, nanos=0.
    assert_eq!(decode_option_duration(1u128 << 127), Some(Duration::ZERO));
  }
}
