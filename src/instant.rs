use std::time::Instant;

use super::*;

/// Atomic version of [`Instant`].
///
/// Values are encoded relative to a process-local baseline pairing
/// `std::time::SystemTime::now()` with `std::time::Instant::now()` (see
/// [`crate::utils::encode_instant_to_duration`] and
/// [`crate::utils::decode_instant_from_duration`]). Within the same process,
/// values in the platform's representable `Instant` range round-trip exactly.
/// Encodings are not portable across processes or restarts: there they only
/// approximate wall-clock time and must not be used as persistent deadlines.
/// System clock adjustments can affect that cross-process interpretation, while
/// behavior across system sleep follows the platform's `Instant` semantics.
///
/// With the `serde` feature, this type retains its `Duration` proxy wire
/// format. For persistent wall-clock values, use [`crate::AtomicSystemTime`].
#[repr(transparent)]
pub struct AtomicInstant(AtomicDuration);

impl core::fmt::Debug for AtomicInstant {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicInstant")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}
impl From<Instant> for AtomicInstant {
  #[inline(always)]
  fn from(instant: Instant) -> Self {
    Self::new(instant)
  }
}
impl AtomicInstant {
  /// Returns the instant corresponding to "now".
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicInstant;
  ///
  /// let now = AtomicInstant::now();
  /// ```
  #[inline(always)]
  pub fn now() -> Self {
    Self::new(Instant::now())
  }

  /// Creates a new `AtomicInstant` with the given `Instant` value.
  #[inline(always)]
  pub fn new(instant: Instant) -> Self {
    Self(AtomicDuration::new(encode_instant_to_duration(instant)))
  }

  /// Loads a value from the atomic instant.
  #[inline(always)]
  pub fn load(&self, order: Ordering) -> Instant {
    decode_instant_from_duration(self.0.load(order))
  }

  /// Stores a value into the atomic instant.
  #[inline(always)]
  pub fn store(&self, instant: Instant, order: Ordering) {
    self.0.store(encode_instant_to_duration(instant), order)
  }

  /// Stores a value into the atomic instant, returning the previous value.
  #[inline(always)]
  pub fn swap(&self, instant: Instant, order: Ordering) -> Instant {
    decode_instant_from_duration(self.0.swap(encode_instant_to_duration(instant), order))
  }

  /// Stores a value into the atomic instant if the current value is the same as the `current`
  /// value.
  #[inline(always)]
  pub fn compare_exchange(
    &self,
    current: Instant,
    new: Instant,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Instant, Instant> {
    match self.0.compare_exchange(
      encode_instant_to_duration(current),
      encode_instant_to_duration(new),
      success,
      failure,
    ) {
      Ok(duration) => Ok(decode_instant_from_duration(duration)),
      Err(duration) => Err(decode_instant_from_duration(duration)),
    }
  }

  /// Stores a value into the atomic instant if the current value is the same as the `current`
  /// value.
  #[inline(always)]
  pub fn compare_exchange_weak(
    &self,
    current: Instant,
    new: Instant,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Instant, Instant> {
    match self.0.compare_exchange_weak(
      encode_instant_to_duration(current),
      encode_instant_to_duration(new),
      success,
      failure,
    ) {
      Ok(duration) => Ok(decode_instant_from_duration(duration)),
      Err(duration) => Err(decode_instant_from_duration(duration)),
    }
  }

  /// Fetches the value and applies a function that can choose whether to store
  /// a new value.
  ///
  /// Returns `Ok(previous_value)` when `f` returns `Some(_)`, and
  /// `Err(previous_value)` when it returns `None`. The closure can run more
  /// than once when another thread changes the value concurrently, but it is
  /// applied only once to the value that is stored.
  ///
  /// `set_order` describes the ordering of the successful update and
  /// `fetch_order` describes failed compare-and-exchange loads. They have the
  /// same requirements as the success and failure orderings of
  /// [`compare_exchange`](Self::compare_exchange).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let start = Instant::now();
  /// let x = AtomicInstant::new(start);
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(start));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |old| Some(old + Duration::from_secs(1))), Ok(start));
  /// ```
  #[inline(always)]
  pub fn try_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<Instant, Instant>
  where
    F: FnMut(Instant) -> Option<Instant>,
  {
    self
      .0
      .try_update(set_order, fetch_order, |duration| {
        f(decode_instant_from_duration(duration)).map(encode_instant_to_duration)
      })
      .map(decode_instant_from_duration)
      .map_err(decode_instant_from_duration)
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
  /// use atomic_time::AtomicInstant;
  /// use std::{time::{Duration, Instant}, sync::atomic::Ordering};
  ///
  /// let now = Instant::now();
  /// let x = AtomicInstant::new(now);
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(now));
  ///
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x + Duration::from_secs(1))), Ok(now));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x + Duration::from_secs(1))), Ok(now + Duration::from_secs(1)));
  /// assert_eq!(x.load(Ordering::SeqCst), now + Duration::from_secs(2));
  /// ```
  #[inline(always)]
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    f: F,
  ) -> Result<Instant, Instant>
  where
    F: FnMut(Instant) -> Option<Instant>,
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
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let start = Instant::now();
  /// let x = AtomicInstant::new(start);
  /// assert_eq!(x.update(Ordering::SeqCst, Ordering::SeqCst, |old| old + Duration::from_secs(1)), start);
  /// assert_eq!(x.load(Ordering::SeqCst), start + Duration::from_secs(1));
  /// ```
  #[inline(always)]
  pub fn update<F>(&self, set_order: Ordering, fetch_order: Ordering, mut f: F) -> Instant
  where
    F: FnMut(Instant) -> Instant,
  {
    decode_instant_from_duration(self.0.update(set_order, fetch_order, |duration| {
      encode_instant_to_duration(f(decode_instant_from_duration(duration)))
    }))
  }

  /// Atomically stores the smaller of the current value and `val`, returning
  /// the previous value.
  ///
  /// The ordering compares values encoded with this process's baseline. It is
  /// meaningful only for `Instant` values using the same process-local
  /// baseline; it does not assign ordering semantics across processes or
  /// process restarts. `order` describes the memory ordering of the
  /// read-modify-write operation. Using [`Acquire`](Ordering::Acquire) makes
  /// its store part relaxed, and using [`Release`](Ordering::Release) makes its
  /// load part relaxed.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let middle = Instant::now();
  /// let low = middle - Duration::from_secs(1);
  /// let high = middle + Duration::from_secs(1);
  /// let x = AtomicInstant::new(middle);
  /// assert_eq!(x.fetch_min(high, Ordering::SeqCst), middle);
  /// assert_eq!(x.fetch_min(low, Ordering::SeqCst), middle);
  /// assert_eq!(x.load(Ordering::SeqCst), low);
  /// ```
  #[inline(always)]
  pub fn fetch_min(&self, val: Instant, order: Ordering) -> Instant {
    decode_instant_from_duration(self.0.fetch_min(encode_instant_to_duration(val), order))
  }

  /// Atomically stores the larger of the current value and `val`, returning
  /// the previous value.
  ///
  /// The ordering compares values encoded with this process's baseline. It is
  /// meaningful only for `Instant` values using the same process-local
  /// baseline; it does not assign ordering semantics across processes or
  /// process restarts. `order` describes the memory ordering of the
  /// read-modify-write operation. Using [`Acquire`](Ordering::Acquire) makes
  /// its store part relaxed, and using [`Release`](Ordering::Release) makes its
  /// load part relaxed.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let middle = Instant::now();
  /// let low = middle - Duration::from_secs(1);
  /// let high = middle + Duration::from_secs(1);
  /// let x = AtomicInstant::new(middle);
  /// assert_eq!(x.fetch_max(low, Ordering::SeqCst), middle);
  /// assert_eq!(x.fetch_max(high, Ordering::SeqCst), middle);
  /// assert_eq!(x.load(Ordering::SeqCst), high);
  /// ```
  #[inline(always)]
  pub fn fetch_max(&self, val: Instant, order: Ordering) -> Instant {
    decode_instant_from_duration(self.0.fetch_max(encode_instant_to_duration(val), order))
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicInstant;
  ///
  /// let is_lock_free = AtomicInstant::is_lock_free();
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
  /// use atomic_time::AtomicInstant;
  ///
  /// const ALWAYS_LOCK_FREE: bool = AtomicInstant::is_always_lock_free();
  /// let _ = ALWAYS_LOCK_FREE;
  /// ```
  #[inline(always)]
  pub const fn is_always_lock_free() -> bool {
    AtomicDuration::is_always_lock_free()
  }

  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[inline(always)]
  pub fn into_inner(self) -> Instant {
    decode_instant_from_duration(self.0.into_inner())
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use core::time::Duration;
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicInstant {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.0.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicInstant {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(decode_instant_from_duration(
        Duration::deserialize(deserializer)?,
      )))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;
  use std::time::Duration;

  #[test]
  fn test_atomic_instant_now() {
    let atomic_instant = AtomicInstant::now();
    // Check that the time is reasonable (not too far from now).
    let now = Instant::now();
    let loaded_instant = atomic_instant.load(Ordering::SeqCst);
    assert!(loaded_instant <= now);
    assert!(loaded_instant >= now - Duration::from_secs(1));
  }

  #[test]
  fn test_atomic_instant_new_and_load() {
    let now = Instant::now();
    let atomic_instant = AtomicInstant::new(now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_instant_store_and_load() {
    let now = Instant::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_instant = AtomicInstant::new(now);
    atomic_instant.store(after_one_sec, Ordering::SeqCst);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_instant_swap() {
    let now = Instant::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_instant = AtomicInstant::new(now);
    let prev_instant = atomic_instant.swap(after_one_sec, Ordering::SeqCst);
    assert_eq!(prev_instant, now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_instant_compare_exchange() {
    let now = Instant::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_instant = AtomicInstant::new(now);
    let result =
      atomic_instant.compare_exchange(now, after_one_sec, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_ok());
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_instant_compare_exchange_weak() {
    let now = Instant::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_instant = AtomicInstant::new(now);

    let mut result;
    loop {
      result = atomic_instant.compare_exchange_weak(
        now,
        after_one_sec,
        Ordering::SeqCst,
        Ordering::SeqCst,
      );
      if result.is_ok() {
        break;
      }
    }
    assert!(result.is_ok());
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_instant_fetch_update() {
    let now = Instant::now();
    let atomic_instant = AtomicInstant::new(now);

    let result = atomic_instant.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |prev| {
      Some(prev + Duration::from_secs(1))
    });
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), now);
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      now + Duration::from_secs(1)
    );
  }

  #[test]
  fn test_atomic_instant_try_update() {
    let start = Instant::now();
    let atomic_instant = AtomicInstant::new(start);

    assert_eq!(
      atomic_instant.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None),
      Err(start)
    );
    assert_eq!(
      atomic_instant.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        Some(current + Duration::from_secs(2))
      }),
      Ok(start)
    );
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      start + Duration::from_secs(2)
    );
  }

  #[test]
  fn test_atomic_instant_update_returns_previous_value() {
    let start = Instant::now();
    let atomic_instant = AtomicInstant::new(start);

    assert_eq!(
      atomic_instant.update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        current + Duration::from_secs(2)
      }),
      start
    );
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      start + Duration::from_secs(2)
    );
  }

  #[test]
  fn test_atomic_instant_fetch_min_and_max() {
    let middle = Instant::now();
    let low = middle.checked_sub(Duration::from_secs(2)).unwrap();
    let high = middle.checked_add(Duration::from_secs(2)).unwrap();
    let atomic_instant = AtomicInstant::new(middle);

    assert_eq!(atomic_instant.fetch_min(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.fetch_min(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.fetch_min(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), low);

    atomic_instant.store(middle, Ordering::SeqCst);
    assert_eq!(atomic_instant.fetch_max(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.fetch_max(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.fetch_max(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), high);
  }

  #[test]
  fn test_atomic_instant_always_lock_free_implies_lock_free() {
    assert!(!AtomicInstant::is_always_lock_free() || AtomicInstant::is_lock_free());
  }

  #[test]
  fn test_atomic_instant_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    // Start from a fixed, known value so we can assert an *exact*
    // final result. The previous version did `load + add + store`,
    // which loses updates under contention (two threads load the
    // same value, each writes load+50ms, only one write survives).
    // Its assertion — "within 200 ms of now" — was satisfied even
    // when 3 of 4 updates were dropped.
    let start = Instant::now();
    let atomic_instant = Arc::new(AtomicInstant::new(start));
    let mut handles = vec![];

    for _ in 0..4 {
      let atomic_clone = atomic_instant.clone();
      let handle = thread::spawn(move || {
        // `fetch_update` retries on conflict, so every thread's
        // increment is guaranteed to stick.
        atomic_clone
          .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
            Some(current + Duration::from_millis(50))
          })
          .expect("closure never returns None");
      });
      handles.push(handle);
    }

    for handle in handles {
      handle.join().unwrap();
    }

    // 4 threads × 50 ms = 200 ms, no lost updates.
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      start + Duration::from_millis(200)
    );
  }

  #[test]
  fn test_atomic_instant_debug() {
    let atomic_instant = AtomicInstant::now();
    let debug_str = format!("{:?}", atomic_instant);
    assert!(debug_str.contains("AtomicInstant"));
  }

  #[test]
  fn test_atomic_instant_from() {
    let now = Instant::now();
    let atomic_instant = AtomicInstant::from(now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_instant_into_inner() {
    let now = Instant::now();
    let atomic_instant = AtomicInstant::new(now);
    assert_eq!(atomic_instant.into_inner(), now);
  }

  #[test]
  fn test_atomic_instant_compare_exchange_failure() {
    let now = Instant::now();
    let other = now + Duration::from_secs(5);
    let atomic_instant = AtomicInstant::new(now);
    let result = atomic_instant.compare_exchange(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[test]
  fn test_atomic_instant_fetch_update_failure() {
    let now = Instant::now();
    let atomic_instant = AtomicInstant::new(now);
    let result = atomic_instant.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_instant_serde_round_trip_past_and_future() {
    let now = Instant::now();
    for instant in [
      now.checked_sub(Duration::from_secs(1)).unwrap(),
      now.checked_add(Duration::from_secs(1)).unwrap(),
    ] {
      let atomic = AtomicInstant::new(instant);
      let serialized = serde_json::to_string(&atomic).unwrap();
      let deserialized: AtomicInstant = serde_json::from_str(&serialized).unwrap();
      assert_eq!(deserialized.load(Ordering::SeqCst), instant);
    }
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_instant_serde_matches_duration_wire_model() {
    let instant = Instant::now();
    let atomic = AtomicInstant::new(instant);
    let wire_model = crate::utils::encode_instant_to_duration(instant);
    assert_eq!(
      serde_json::to_string(&atomic).unwrap(),
      serde_json::to_string(&wire_model).unwrap()
    );
  }

  #[test]
  fn test_atomic_instant_past_value() {
    use std::thread;

    let past = Instant::now();
    thread::sleep(Duration::from_millis(10));
    let now = Instant::now();

    // Store a past instant and verify roundtrip
    let atomic = AtomicInstant::new(now);
    atomic.store(past, Ordering::SeqCst);
    let loaded = atomic.load(Ordering::SeqCst);
    assert!(loaded < now);
    assert_eq!(loaded, past);
  }

  #[test]
  fn decode_extreme_instant_falls_back_to_baseline() {
    // Inputs outside the platform Instant range use the process baseline as a
    // fallback rather than saturating an Instant value.
    let max_dur = Duration::new(u64::MAX, 999_999_999);
    let decoded = crate::utils::decode_instant_from_duration(max_dur);
    let other_extreme = Duration::new(u64::MAX, 999_999_998);
    assert_eq!(
      decoded,
      crate::utils::decode_instant_from_duration(other_extreme)
    );
  }

  #[cfg(feature = "serde")]
  #[test]
  fn deserialize_extreme_instant_uses_baseline_fallback() {
    // Preserve the existing Ok deserialization behavior for an extreme wire
    // value; its decoded Instant falls back to the process baseline.
    let json = r#"{"secs":18446744073709551615,"nanos":999999999}"#;
    let result: Result<AtomicInstant, _> = serde_json::from_str(json);
    let atomic = result.expect("extreme Instant deserialization remains Ok");
    assert_eq!(
      atomic.load(Ordering::SeqCst),
      crate::utils::decode_instant_from_duration(Duration::new(u64::MAX, 999_999_999))
    );
  }
}
