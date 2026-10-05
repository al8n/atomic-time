use std::time::Instant;

use super::*;

/// Atomic version of [`Option<Instant>`].
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
/// With the `serde` feature, this type retains its `Option<Duration>` proxy
/// wire format. For persistent wall-clock values, use
/// [`crate::AtomicOptionSystemTime`].
#[repr(transparent)]
pub struct AtomicOptionInstant(AtomicOptionDuration);

impl core::fmt::Debug for AtomicOptionInstant {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicOptionInstant")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}
impl Default for AtomicOptionInstant {
  /// Equivalent to `Option::<Instant>::None`.
  #[inline(always)]
  fn default() -> Self {
    Self::none()
  }
}
impl From<Option<Instant>> for AtomicOptionInstant {
  #[inline(always)]
  fn from(instant: Option<Instant>) -> Self {
    Self::new(instant)
  }
}

impl AtomicOptionInstant {
  /// Equivalent to atomic version `Option::<Instant>::None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionInstant;
  ///
  /// let none = AtomicOptionInstant::none();
  /// assert_eq!(none.load(std::sync::atomic::Ordering::SeqCst), None);
  /// ```
  #[inline(always)]
  pub const fn none() -> Self {
    Self(AtomicOptionDuration::new(None))
  }

  /// Returns the instant corresponding to "now".
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicOptionInstant;
  ///
  /// let now = AtomicOptionInstant::now();
  /// ```
  #[inline(always)]
  pub fn now() -> Self {
    Self::new(Some(Instant::now()))
  }

  /// Creates a new `AtomicOptionInstant` with the given `Instant` value.
  #[inline(always)]
  pub fn new(instant: Option<Instant>) -> Self {
    Self(AtomicOptionDuration::new(
      instant.map(encode_instant_to_duration),
    ))
  }

  /// Loads a value from the atomic instant.
  #[inline(always)]
  pub fn load(&self, order: Ordering) -> Option<Instant> {
    self.0.load(order).map(decode_instant_from_duration)
  }

  /// Stores a value into the atomic instant.
  #[inline(always)]
  pub fn store(&self, instant: Option<Instant>, order: Ordering) {
    self.0.store(instant.map(encode_instant_to_duration), order)
  }

  /// Stores a value into the atomic instant, returning the previous value.
  #[inline(always)]
  pub fn swap(&self, instant: Option<Instant>, order: Ordering) -> Option<Instant> {
    self
      .0
      .swap(instant.map(encode_instant_to_duration), order)
      .map(decode_instant_from_duration)
  }

  /// Stores a value into the atomic instant if the current value is the same as the `current`
  /// value.
  #[inline(always)]
  pub fn compare_exchange(
    &self,
    current: Option<Instant>,
    new: Option<Instant>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<Instant>, Option<Instant>> {
    match self.0.compare_exchange(
      current.map(encode_instant_to_duration),
      new.map(encode_instant_to_duration),
      success,
      failure,
    ) {
      Ok(duration) => Ok(duration.map(decode_instant_from_duration)),
      Err(duration) => Err(duration.map(decode_instant_from_duration)),
    }
  }

  /// Stores a value into the atomic instant if the current value is the same as the `current`
  /// value.
  #[inline(always)]
  pub fn compare_exchange_weak(
    &self,
    current: Option<Instant>,
    new: Option<Instant>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<Instant>, Option<Instant>> {
    match self.0.compare_exchange_weak(
      current.map(encode_instant_to_duration),
      new.map(encode_instant_to_duration),
      success,
      failure,
    ) {
      Ok(duration) => Ok(duration.map(decode_instant_from_duration)),
      Err(duration) => Err(duration.map(decode_instant_from_duration)),
    }
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
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let start = Instant::now();
  /// let x = AtomicOptionInstant::new(Some(start));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(Some(start)));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |old| Some(old.map(|instant| instant + Duration::from_secs(1)))), Ok(Some(start)));
  /// ```
  #[inline(always)]
  pub fn try_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<Option<Instant>, Option<Instant>>
  where
    F: FnMut(Option<Instant>) -> Option<Option<Instant>>,
  {
    self
      .0
      .try_update(set_order, fetch_order, |duration| {
        f(duration.map(decode_instant_from_duration))
          .map(|instant| instant.map(encode_instant_to_duration))
      })
      .map(|duration| duration.map(decode_instant_from_duration))
      .map_err(|duration| duration.map(decode_instant_from_duration))
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
  /// use atomic_time::AtomicOptionInstant;
  /// use std::{time::{Duration, Instant}, sync::atomic::Ordering};
  ///
  /// let now = Instant::now();
  /// let x = AtomicOptionInstant::none();
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(None));
  /// x.store(Some(now), Ordering::SeqCst);
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now)));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now + Duration::from_secs(1))));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now + Duration::from_secs(2))));
  /// assert_eq!(x.load(Ordering::SeqCst), Some(now + Duration::from_secs(3)));
  /// ```
  #[inline(always)]
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    f: F,
  ) -> Result<Option<Instant>, Option<Instant>>
  where
    F: FnMut(Option<Instant>) -> Option<Option<Instant>>,
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
  /// use atomic_time::AtomicOptionInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let start = Instant::now();
  /// let x = AtomicOptionInstant::new(Some(start));
  /// assert_eq!(x.update(Ordering::SeqCst, Ordering::SeqCst, |old| old.map(|instant| instant + Duration::from_secs(1))), Some(start));
  /// assert_eq!(x.load(Ordering::SeqCst), Some(start + Duration::from_secs(1)));
  /// ```
  #[inline(always)]
  pub fn update<F>(&self, set_order: Ordering, fetch_order: Ordering, mut f: F) -> Option<Instant>
  where
    F: FnMut(Option<Instant>) -> Option<Instant>,
  {
    self
      .0
      .update(set_order, fetch_order, |duration| {
        f(duration.map(decode_instant_from_duration)).map(encode_instant_to_duration)
      })
      .map(decode_instant_from_duration)
  }

  /// Atomically stores the smaller of the current value and `val`, returning
  /// the previous value.
  ///
  /// `None` is ordered before every `Some` value. `Some` values are ordered by
  /// the process-local baseline encoding. This ordering is meaningful only for
  /// values using the same process-local baseline; it does not assign ordering
  /// semantics across processes or process restarts. `order` describes the
  /// memory ordering of the read-modify-write operation. Using
  /// [`Acquire`](Ordering::Acquire) makes its store part relaxed, and using
  /// [`Release`](Ordering::Release) makes its load part relaxed.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let middle = Instant::now();
  /// let low = middle - Duration::from_secs(1);
  /// let high = middle + Duration::from_secs(1);
  /// let x = AtomicOptionInstant::new(Some(middle));
  /// assert_eq!(x.fetch_min(Some(high), Ordering::SeqCst), Some(middle));
  /// assert_eq!(x.fetch_min(Some(low), Ordering::SeqCst), Some(middle));
  /// assert_eq!(x.load(Ordering::SeqCst), Some(low));
  /// ```
  #[inline(always)]
  pub fn fetch_min(&self, val: Option<Instant>, order: Ordering) -> Option<Instant> {
    self
      .0
      .fetch_min(val.map(encode_instant_to_duration), order)
      .map(decode_instant_from_duration)
  }

  /// Atomically stores the larger of the current value and `val`, returning
  /// the previous value.
  ///
  /// `None` is ordered before every `Some` value. `Some` values are ordered by
  /// the process-local baseline encoding. This ordering is meaningful only for
  /// values using the same process-local baseline; it does not assign ordering
  /// semantics across processes or process restarts. `order` describes the
  /// memory ordering of the read-modify-write operation. Using
  /// [`Acquire`](Ordering::Acquire) makes its store part relaxed, and using
  /// [`Release`](Ordering::Release) makes its load part relaxed.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionInstant;
  /// use std::{sync::atomic::Ordering, time::{Duration, Instant}};
  ///
  /// let high = Instant::now() + Duration::from_secs(1);
  /// let x = AtomicOptionInstant::none();
  /// assert_eq!(x.fetch_max(None, Ordering::SeqCst), None);
  /// assert_eq!(x.fetch_max(Some(high), Ordering::SeqCst), None);
  /// assert_eq!(x.load(Ordering::SeqCst), Some(high));
  /// ```
  #[inline(always)]
  pub fn fetch_max(&self, val: Option<Instant>, order: Ordering) -> Option<Instant> {
    self
      .0
      .fetch_max(val.map(encode_instant_to_duration), order)
      .map(decode_instant_from_duration)
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicOptionInstant;
  ///
  /// let is_lock_free = AtomicOptionInstant::is_lock_free();
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
  /// use atomic_time::AtomicOptionInstant;
  ///
  /// const ALWAYS_LOCK_FREE: bool = AtomicOptionInstant::is_always_lock_free();
  /// let _ = ALWAYS_LOCK_FREE;
  /// ```
  #[inline(always)]
  pub const fn is_always_lock_free() -> bool {
    AtomicOptionDuration::is_always_lock_free()
  }

  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[inline(always)]
  pub fn into_inner(self) -> Option<Instant> {
    self.0.into_inner().map(decode_instant_from_duration)
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use core::time::Duration;
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicOptionInstant {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.0.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicOptionInstant {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(
        Option::<Duration>::deserialize(deserializer)?.map(decode_instant_from_duration),
      ))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;
  use std::time::Duration;

  #[test]
  fn test_atomic_option_instant_none() {
    let atomic_instant = AtomicOptionInstant::none();
    assert_eq!(atomic_instant.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_instant_now() {
    let atomic_instant = AtomicOptionInstant::now();
    let now = Instant::now();
    if let Some(loaded_instant) = atomic_instant.load(Ordering::SeqCst) {
      assert!(loaded_instant <= now);
      assert!(loaded_instant >= now - Duration::from_secs(1));
    } else {
      panic!("AtomicOptionInstant::now() should not be None");
    }
  }

  #[test]
  fn test_atomic_option_instant_new_and_load() {
    let now = Some(Instant::now());
    let atomic_instant = AtomicOptionInstant::new(now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_option_instant_store_and_load() {
    let now = Some(Instant::now());
    let after_one_sec = now.map(|t| t + Duration::from_secs(1));
    let atomic_instant = AtomicOptionInstant::new(now);
    atomic_instant.store(after_one_sec, Ordering::SeqCst);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_option_instant_swap() {
    let now = Some(Instant::now());
    let after_one_sec = now.map(|t| t + Duration::from_secs(1));
    let atomic_instant = AtomicOptionInstant::new(now);
    let prev_instant = atomic_instant.swap(after_one_sec, Ordering::SeqCst);
    assert_eq!(prev_instant, now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_option_instant_compare_exchange() {
    let now = Some(Instant::now());
    let after_one_sec = now.map(|t| t + Duration::from_secs(1));
    let atomic_instant = AtomicOptionInstant::new(now);
    let result =
      atomic_instant.compare_exchange(now, after_one_sec, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_ok());
    assert_eq!(atomic_instant.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_option_instant_compare_exchange_weak() {
    let now = Some(Instant::now());
    let after_one_sec = now.map(|t| t + Duration::from_secs(1));
    let atomic_instant = AtomicOptionInstant::new(now);

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
  fn test_atomic_option_instant_fetch_update() {
    let now = Some(Instant::now());
    let atomic_instant = AtomicOptionInstant::new(now);

    let result = atomic_instant.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |prev| {
      Some(prev.map(|t| t + Duration::from_secs(1)))
    });
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), now);
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      now.map(|t| t + Duration::from_secs(1))
    );
  }

  #[test]
  fn test_atomic_option_instant_try_update() {
    let start = Instant::now();
    let atomic_instant = AtomicOptionInstant::new(Some(start));

    assert_eq!(
      atomic_instant.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None),
      Err(Some(start))
    );
    assert_eq!(
      atomic_instant.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        Some(current.map(|instant| instant + Duration::from_secs(2)))
      }),
      Ok(Some(start))
    );
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      Some(start + Duration::from_secs(2))
    );
  }

  #[test]
  fn test_atomic_option_instant_update_returns_previous_value() {
    let start = Instant::now();
    let atomic_instant = AtomicOptionInstant::new(Some(start));

    assert_eq!(
      atomic_instant.update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        current.map(|instant| instant + Duration::from_secs(2))
      }),
      Some(start)
    );
    assert_eq!(
      atomic_instant.load(Ordering::SeqCst),
      Some(start + Duration::from_secs(2))
    );
  }

  #[test]
  fn test_atomic_option_instant_fetch_min_and_max() {
    let middle = Instant::now();
    let low = middle.checked_sub(Duration::from_secs(2)).unwrap();
    let high = middle.checked_add(Duration::from_secs(2)).unwrap();
    let atomic_instant = AtomicOptionInstant::new(Some(middle));

    assert_eq!(
      atomic_instant.fetch_min(Some(high), Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(middle));
    assert_eq!(
      atomic_instant.fetch_min(Some(middle), Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(middle));
    assert_eq!(
      atomic_instant.fetch_min(Some(low), Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(low));

    atomic_instant.store(Some(middle), Ordering::SeqCst);
    assert_eq!(
      atomic_instant.fetch_max(None, Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(middle));
    assert_eq!(
      atomic_instant.fetch_max(Some(middle), Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(middle));
    assert_eq!(
      atomic_instant.fetch_max(Some(high), Ordering::SeqCst),
      Some(middle)
    );
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(high));

    atomic_instant.store(None, Ordering::SeqCst);
    assert_eq!(atomic_instant.fetch_min(None, Ordering::SeqCst), None);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), None);
    assert_eq!(atomic_instant.fetch_max(None, Ordering::SeqCst), None);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), None);
    assert_eq!(atomic_instant.fetch_max(Some(low), Ordering::SeqCst), None);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), Some(low));
  }

  #[test]
  fn test_atomic_option_instant_always_lock_free_implies_lock_free() {
    assert!(!AtomicOptionInstant::is_always_lock_free() || AtomicOptionInstant::is_lock_free());
  }

  #[test]
  fn test_atomic_option_instant_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    // Fixed starting value + CAS loop = exact final result. The
    // earlier implementation did `load + add + store` (not a CAS) and
    // asserted "within 4 seconds of now", which even a single
    // surviving write would satisfy.
    let start = Instant::now();
    let atomic_time = Arc::new(AtomicOptionInstant::new(Some(start)));
    let mut handles = vec![];

    for _ in 0..4 {
      let atomic_clone = Arc::clone(&atomic_time);
      let handle = thread::spawn(move || {
        atomic_clone
          .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
            current.map(|t| Some(t + Duration::from_secs(1)))
          })
          .expect("atomic is always Some in this test");
      });
      handles.push(handle);
    }

    for handle in handles {
      handle.join().unwrap();
    }

    // 4 threads × 1 second = 4 seconds, no lost updates.
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      Some(start + Duration::from_secs(4))
    );
  }

  #[test]
  fn test_atomic_option_instant_debug() {
    let atomic_instant = AtomicOptionInstant::now();
    let debug_str = format!("{:?}", atomic_instant);
    assert!(debug_str.contains("AtomicOptionInstant"));
  }

  #[test]
  fn test_atomic_option_instant_default() {
    let atomic_instant = AtomicOptionInstant::default();
    assert_eq!(atomic_instant.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_instant_from() {
    let now = Some(Instant::now());
    let atomic_instant = AtomicOptionInstant::from(now);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_option_instant_from_none() {
    let atomic_instant = AtomicOptionInstant::from(None);
    assert_eq!(atomic_instant.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_instant_into_inner() {
    let now = Some(Instant::now());
    let atomic_instant = AtomicOptionInstant::new(now);
    assert_eq!(atomic_instant.into_inner(), now);
  }

  #[test]
  fn test_atomic_option_instant_into_inner_none() {
    let atomic_instant = AtomicOptionInstant::none();
    assert_eq!(atomic_instant.into_inner(), None);
  }

  #[test]
  fn test_atomic_option_instant_compare_exchange_failure() {
    let now = Some(Instant::now());
    let other = now.map(|t| t + Duration::from_secs(5));
    let atomic_instant = AtomicOptionInstant::new(now);
    let result = atomic_instant.compare_exchange(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[test]
  fn test_atomic_option_instant_compare_exchange_weak_failure() {
    let now = Some(Instant::now());
    let other = now.map(|t| t + Duration::from_secs(5));
    let atomic_instant = AtomicOptionInstant::new(now);
    let result =
      atomic_instant.compare_exchange_weak(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
  }

  #[test]
  fn test_atomic_option_instant_fetch_update_failure() {
    let now = Some(Instant::now());
    let atomic_instant = AtomicOptionInstant::new(now);
    let result = atomic_instant.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_option_instant_serde_round_trip() {
    let now = Instant::now();
    for instant in [
      None,
      Some(now.checked_sub(Duration::from_secs(1)).unwrap()),
      Some(now.checked_add(Duration::from_secs(1)).unwrap()),
    ] {
      let atomic = AtomicOptionInstant::new(instant);
      let serialized = serde_json::to_string(&atomic).unwrap();
      let deserialized: AtomicOptionInstant = serde_json::from_str(&serialized).unwrap();
      assert_eq!(deserialized.load(Ordering::SeqCst), instant);
    }
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_option_instant_serde_matches_option_duration_wire_model() {
    for instant in [None, Some(Instant::now())] {
      let atomic = AtomicOptionInstant::new(instant);
      let wire_model = instant.map(crate::utils::encode_instant_to_duration);
      assert_eq!(
        serde_json::to_string(&atomic).unwrap(),
        serde_json::to_string(&wire_model).unwrap()
      );
    }
  }

  #[test]
  fn decode_extreme_option_instant_falls_back_to_baseline() {
    let max_dur = Duration::new(u64::MAX, 999_999_999);
    let decoded = crate::utils::decode_instant_from_duration(max_dur);
    // Inputs outside the platform Instant range use the process baseline as a
    // fallback rather than saturating an Instant value.
    let other_extreme = Duration::new(u64::MAX, 999_999_998);
    assert_eq!(
      decoded,
      crate::utils::decode_instant_from_duration(other_extreme)
    );
  }

  #[cfg(feature = "serde")]
  #[test]
  fn deserialize_extreme_option_instant_uses_baseline_fallback() {
    // Preserve the existing Ok deserialization behavior for an extreme wire
    // value; its decoded Instant falls back to the process baseline.
    let json = r#"{"secs":18446744073709551615,"nanos":999999999}"#;
    let result: Result<AtomicOptionInstant, _> = serde_json::from_str(json);
    let atomic = result.expect("extreme Option<Instant> deserialization remains Ok");
    assert_eq!(
      atomic.load(Ordering::SeqCst),
      Some(crate::utils::decode_instant_from_duration(Duration::new(
        u64::MAX,
        999_999_999
      )))
    );
  }
}
