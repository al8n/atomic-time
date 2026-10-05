use core::sync::atomic::Ordering;
use std::time::SystemTime;

use crate::AtomicDuration;

/// An atomic version of [`std::time::SystemTime`].
///
/// Only [`SystemTime`] values at or after [`SystemTime::UNIX_EPOCH`] are supported.
#[repr(transparent)]
pub struct AtomicSystemTime(AtomicDuration);

impl core::fmt::Debug for AtomicSystemTime {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicSystemTime")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}

impl From<SystemTime> for AtomicSystemTime {
  /// # Panics
  ///
  /// Panics if the given `SystemTime` value is earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  fn from(system_time: SystemTime) -> Self {
    Self::new(system_time)
  }
}

impl AtomicSystemTime {
  /// Returns the system time corresponding to "now".
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicSystemTime;
  ///
  /// let sys_time = AtomicSystemTime::now();
  /// ```
  #[inline(always)]
  pub fn now() -> Self {
    Self::new(SystemTime::now())
  }

  /// Creates a new `AtomicSystemTime` with the given `SystemTime` value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  pub fn new(system_time: SystemTime) -> Self {
    Self(AtomicDuration::new(
      system_time.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
    ))
  }

  /// Loads a value from the atomic system time.
  #[inline(always)]
  pub fn load(&self, order: Ordering) -> SystemTime {
    SystemTime::UNIX_EPOCH + self.0.load(order)
  }

  /// Stores a value into the atomic system time.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  pub fn store(&self, system_time: SystemTime, order: Ordering) {
    self.0.store(
      system_time.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
      order,
    )
  }

  /// Stores a value into the atomic system time, returning the previous value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  pub fn swap(&self, system_time: SystemTime, order: Ordering) -> SystemTime {
    SystemTime::UNIX_EPOCH
      + self.0.swap(
        system_time.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
        order,
      )
  }

  /// Stores a value into the atomic system time if the current value is the same as the `current`
  /// value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  pub fn compare_exchange(
    &self,
    current: SystemTime,
    new: SystemTime,
    success: Ordering,
    failure: Ordering,
  ) -> Result<SystemTime, SystemTime> {
    match self.0.compare_exchange(
      current.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
      new.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
      success,
      failure,
    ) {
      Ok(duration) => Ok(SystemTime::UNIX_EPOCH + duration),
      Err(duration) => Err(SystemTime::UNIX_EPOCH + duration),
    }
  }

  /// Stores a value into the atomic system time if the current value is the same as the `current`
  /// value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[inline(always)]
  pub fn compare_exchange_weak(
    &self,
    current: SystemTime,
    new: SystemTime,
    success: Ordering,
    failure: Ordering,
  ) -> Result<SystemTime, SystemTime> {
    match self.0.compare_exchange_weak(
      current.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
      new.duration_since(SystemTime::UNIX_EPOCH).unwrap(),
      success,
      failure,
    ) {
      Ok(duration) => Ok(SystemTime::UNIX_EPOCH + duration),
      Err(duration) => Err(SystemTime::UNIX_EPOCH + duration),
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
  /// # Panics
  ///
  /// Panics if the orderings are invalid for
  /// [`compare_exchange`](Self::compare_exchange), or if the function returns
  /// a `SystemTime` value earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicSystemTime;
  /// use std::{sync::atomic::Ordering, time::{Duration, SystemTime}};
  ///
  /// let start = SystemTime::UNIX_EPOCH + Duration::from_secs(7);
  /// let x = AtomicSystemTime::new(start);
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(start));
  /// assert_eq!(x.try_update(Ordering::SeqCst, Ordering::SeqCst, |old| Some(old + Duration::from_secs(1))), Ok(start));
  /// ```
  #[inline(always)]
  pub fn try_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<SystemTime, SystemTime>
  where
    F: FnMut(SystemTime) -> Option<SystemTime>,
  {
    self
      .0
      .try_update(set_order, fetch_order, |duration| {
        f(SystemTime::UNIX_EPOCH + duration)
          .map(|system_time| system_time.duration_since(SystemTime::UNIX_EPOCH).unwrap())
      })
      .map(|duration| SystemTime::UNIX_EPOCH + duration)
      .map_err(|duration| SystemTime::UNIX_EPOCH + duration)
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
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicSystemTime;
  /// use std::{time::{Duration, SystemTime}, sync::atomic::Ordering};
  ///
  /// let now = SystemTime::now();
  /// let x = AtomicSystemTime::new(now);
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
  ) -> Result<SystemTime, SystemTime>
  where
    F: FnMut(SystemTime) -> Option<SystemTime>,
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
  /// [`compare_exchange`](Self::compare_exchange), or if the function returns
  /// a `SystemTime` value earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicSystemTime;
  /// use std::{sync::atomic::Ordering, time::{Duration, SystemTime}};
  ///
  /// let start = SystemTime::UNIX_EPOCH + Duration::from_secs(7);
  /// let x = AtomicSystemTime::new(start);
  /// assert_eq!(x.update(Ordering::SeqCst, Ordering::SeqCst, |old| old + Duration::from_secs(1)), start);
  /// assert_eq!(x.load(Ordering::SeqCst), start + Duration::from_secs(1));
  /// ```
  #[inline(always)]
  pub fn update<F>(&self, set_order: Ordering, fetch_order: Ordering, mut f: F) -> SystemTime
  where
    F: FnMut(SystemTime) -> SystemTime,
  {
    SystemTime::UNIX_EPOCH
      + self.0.update(set_order, fetch_order, |duration| {
        f(SystemTime::UNIX_EPOCH + duration)
          .duration_since(SystemTime::UNIX_EPOCH)
          .unwrap()
      })
  }

  /// Atomically stores the smaller of the current value and `val`, returning
  /// the previous value.
  ///
  /// Values are ordered by their duration from [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  /// `order` describes the memory ordering of the read-modify-write operation.
  /// Using [`Acquire`](Ordering::Acquire) makes its store part relaxed, and
  /// using [`Release`](Ordering::Release) makes its load part relaxed.
  ///
  /// # Panics
  ///
  /// Panics if `val` is earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicSystemTime;
  /// use std::{sync::atomic::Ordering, time::{Duration, SystemTime}};
  ///
  /// let start = SystemTime::UNIX_EPOCH + Duration::from_secs(5);
  /// let x = AtomicSystemTime::new(start);
  /// assert_eq!(x.fetch_min(start + Duration::from_secs(2), Ordering::SeqCst), start);
  /// assert_eq!(x.fetch_min(start - Duration::from_secs(1), Ordering::SeqCst), start);
  /// assert_eq!(x.load(Ordering::SeqCst), start - Duration::from_secs(1));
  /// ```
  #[inline(always)]
  pub fn fetch_min(&self, val: SystemTime, order: Ordering) -> SystemTime {
    SystemTime::UNIX_EPOCH
      + self
        .0
        .fetch_min(val.duration_since(SystemTime::UNIX_EPOCH).unwrap(), order)
  }

  /// Atomically stores the larger of the current value and `val`, returning
  /// the previous value.
  ///
  /// Values are ordered by their duration from [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  /// `order` describes the memory ordering of the read-modify-write operation.
  /// Using [`Acquire`](Ordering::Acquire) makes its store part relaxed, and
  /// using [`Release`](Ordering::Release) makes its load part relaxed.
  ///
  /// # Panics
  ///
  /// Panics if `val` is earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicSystemTime;
  /// use std::{sync::atomic::Ordering, time::{Duration, SystemTime}};
  ///
  /// let start = SystemTime::UNIX_EPOCH + Duration::from_secs(5);
  /// let x = AtomicSystemTime::new(start);
  /// assert_eq!(x.fetch_max(start - Duration::from_secs(2), Ordering::SeqCst), start);
  /// assert_eq!(x.fetch_max(start + Duration::from_secs(1), Ordering::SeqCst), start);
  /// assert_eq!(x.load(Ordering::SeqCst), start + Duration::from_secs(1));
  /// ```
  #[inline(always)]
  pub fn fetch_max(&self, val: SystemTime, order: Ordering) -> SystemTime {
    SystemTime::UNIX_EPOCH
      + self
        .0
        .fetch_max(val.duration_since(SystemTime::UNIX_EPOCH).unwrap(), order)
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicSystemTime;
  ///
  /// let is_lock_free = AtomicSystemTime::is_lock_free();
  /// ```
  #[inline(always)]
  pub fn is_lock_free() -> bool {
    AtomicDuration::is_lock_free()
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
  /// use atomic_time::AtomicSystemTime;
  ///
  /// const ALWAYS_LOCK_FREE: bool = AtomicSystemTime::is_always_lock_free();
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
  pub fn into_inner(self) -> SystemTime {
    SystemTime::UNIX_EPOCH + self.0.into_inner()
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicSystemTime {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicSystemTime {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(SystemTime::deserialize(deserializer)?))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;
  use std::time::Duration;

  #[test]
  fn test_atomic_system_time_now() {
    let atomic_time = AtomicSystemTime::now();
    // As SystemTime::now is very precise, this test needs to be lenient with timing.
    // Just check that the time is not the UNIX_EPOCH.
    assert_ne!(atomic_time.load(Ordering::SeqCst), SystemTime::UNIX_EPOCH);
  }

  #[test]
  fn test_atomic_system_time_new_and_load() {
    let now = SystemTime::now();
    let atomic_time = AtomicSystemTime::new(now);
    assert_eq!(atomic_time.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_system_time_store_and_load() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicSystemTime::new(now);
    atomic_time.store(after_one_sec, Ordering::SeqCst);
    assert_eq!(atomic_time.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_system_time_swap() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicSystemTime::new(now);
    let prev_time = atomic_time.swap(after_one_sec, Ordering::SeqCst);
    assert_eq!(prev_time, now);
    assert_eq!(atomic_time.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_system_time_compare_exchange_weak() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let after_two_secs = now + Duration::from_secs(2);
    let atomic_time = AtomicSystemTime::new(now);

    // Successful compare_exchange_weak
    let mut result;
    loop {
      result =
        atomic_time.compare_exchange_weak(now, after_one_sec, Ordering::SeqCst, Ordering::SeqCst);
      if result.is_ok() {
        break;
      }
    }
    assert!(result.is_ok());
    assert_eq!(atomic_time.load(Ordering::SeqCst), after_one_sec);

    // Failed compare_exchange_weak
    let result =
      atomic_time.compare_exchange_weak(now, after_two_secs, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), after_one_sec);
  }

  #[test]
  fn test_atomic_system_time_compare_exchange() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicSystemTime::new(now);
    let result =
      atomic_time.compare_exchange(now, after_one_sec, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_ok());
    assert_eq!(atomic_time.load(Ordering::SeqCst), after_one_sec);
  }

  #[test]
  fn test_atomic_system_time_fetch_update() {
    let now = SystemTime::now();
    let atomic_time = AtomicSystemTime::new(now);

    // Update the time by adding 1 second
    let result = atomic_time.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |prev| {
      Some(prev + Duration::from_secs(1))
    });
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), now);
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      now + Duration::from_secs(1)
    );

    // Trying an update that returns None, should not change the value
    let result = atomic_time.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now + Duration::from_secs(1));
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      now + Duration::from_secs(1)
    );
  }

  #[test]
  fn test_atomic_system_time_try_update() {
    let start = SystemTime::UNIX_EPOCH + Duration::from_secs(10);
    let atomic_time = AtomicSystemTime::new(start);

    assert_eq!(
      atomic_time.try_update(Ordering::SeqCst, Ordering::SeqCst, |_| None),
      Err(start)
    );
    assert_eq!(
      atomic_time.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        Some(current + Duration::from_secs(2))
      }),
      Ok(start)
    );
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      start + Duration::from_secs(2)
    );
  }

  #[test]
  fn test_atomic_system_time_update_returns_previous_value() {
    let start = SystemTime::UNIX_EPOCH + Duration::from_secs(10);
    let atomic_time = AtomicSystemTime::new(start);

    assert_eq!(
      atomic_time.update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        current + Duration::from_secs(2)
      }),
      start
    );
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      start + Duration::from_secs(2)
    );
  }

  #[test]
  fn test_atomic_system_time_fetch_min_and_max() {
    let low = SystemTime::UNIX_EPOCH + Duration::from_secs(10);
    let middle = low + Duration::from_secs(5);
    let high = middle + Duration::from_secs(5);
    let atomic_time = AtomicSystemTime::new(middle);

    assert_eq!(atomic_time.fetch_min(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_time.fetch_min(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_time.fetch_min(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), low);

    atomic_time.store(middle, Ordering::SeqCst);
    assert_eq!(atomic_time.fetch_max(low, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_time.fetch_max(middle, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), middle);
    assert_eq!(atomic_time.fetch_max(high, Ordering::SeqCst), middle);
    assert_eq!(atomic_time.load(Ordering::SeqCst), high);
  }

  #[test]
  fn test_atomic_system_time_always_lock_free_implies_lock_free() {
    assert!(!AtomicSystemTime::is_always_lock_free() || AtomicSystemTime::is_lock_free());
  }

  #[test]
  #[should_panic]
  fn test_atomic_system_time_fetch_min_before_epoch_panics() {
    let atomic_time = AtomicSystemTime::new(SystemTime::UNIX_EPOCH);
    atomic_time.fetch_min(
      SystemTime::UNIX_EPOCH - Duration::from_secs(1),
      Ordering::SeqCst,
    );
  }

  #[test]
  #[cfg(feature = "std")]
  fn test_atomic_system_time_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    // Start from a fixed, known value so we can assert an *exact*
    // final result. The previous version used `load + add + store`,
    // which loses updates under contention, and asserted only that
    // the final time was in the future — true even if every
    // concurrent update was dropped.
    let start = SystemTime::now();
    let atomic_time = Arc::new(AtomicSystemTime::new(start));
    let mut handles = vec![];

    for _ in 0..4 {
      let atomic_clone = atomic_time.clone();
      let handle = thread::spawn(move || {
        atomic_clone
          .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
            Some(current + Duration::from_secs(1))
          })
          .expect("closure never returns None");
      });
      handles.push(handle);
    }

    for handle in handles {
      handle.join().unwrap();
    }

    // 4 threads × 1 second = 4 seconds, no lost updates.
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      start + Duration::from_secs(4)
    );
  }

  #[test]
  fn test_atomic_system_time_debug() {
    let atomic_time = AtomicSystemTime::now();
    let debug_str = format!("{:?}", atomic_time);
    assert!(debug_str.contains("AtomicSystemTime"));
  }

  #[test]
  fn test_atomic_system_time_from() {
    let now = SystemTime::now();
    let atomic_time = AtomicSystemTime::from(now);
    assert_eq!(atomic_time.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_system_time_into_inner() {
    let now = SystemTime::now();
    let atomic_time = AtomicSystemTime::new(now);
    assert_eq!(atomic_time.into_inner(), now);
  }

  #[test]
  fn test_atomic_system_time_compare_exchange_failure() {
    let now = SystemTime::now();
    let other = now + Duration::from_secs(5);
    let atomic_time = AtomicSystemTime::new(now);
    let result = atomic_time.compare_exchange(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[test]
  fn test_atomic_system_time_compare_exchange_weak_failure() {
    let now = SystemTime::now();
    let other = now + Duration::from_secs(5);
    let atomic_time = AtomicSystemTime::new(now);
    let result =
      atomic_time.compare_exchange_weak(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_system_time_serde() {
    let now = SystemTime::now();
    let atomic = AtomicSystemTime::new(now);
    let serialized = serde_json::to_string(&atomic).unwrap();
    let deserialized: AtomicSystemTime = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized.load(Ordering::SeqCst), now,);
  }
}
