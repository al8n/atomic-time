use core::sync::atomic::Ordering;
use std::time::SystemTime;

use crate::AtomicOptionDuration;

/// An atomic version of [`Option<std::time::SystemTime>`].
#[repr(transparent)]
pub struct AtomicOptionSystemTime(AtomicOptionDuration);

impl core::fmt::Debug for AtomicOptionSystemTime {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicOptionSystemTime")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}
impl Default for AtomicOptionSystemTime {
  /// Equivalent to `Option::<SystemTime>::None`.
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn default() -> Self {
    Self::none()
  }
}
impl From<Option<SystemTime>> for AtomicOptionSystemTime {
  /// # Panics
  ///
  /// Panics if the given `SystemTime` value is earlier than [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  fn from(system_time: Option<SystemTime>) -> Self {
    Self::new(system_time)
  }
}

impl AtomicOptionSystemTime {
  /// Equivalent to atomic version `Option::<SystemTime>>::None`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionSystemTime;
  ///
  /// let none = AtomicOptionSystemTime::none();
  /// assert_eq!(none.load(std::sync::atomic::Ordering::SeqCst), None);
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub const fn none() -> Self {
    Self(AtomicOptionDuration::new(None))
  }

  /// Returns the system time corresponding to "now".
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicOptionSystemTime;
  ///
  /// let sys_time = AtomicOptionSystemTime::now();
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn now() -> Self {
    Self::new(Some(SystemTime::now()))
  }

  /// Creates a new `AtomicOptionSystemTime` with the given `SystemTime` value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn new(system_time: Option<SystemTime>) -> Self {
    Self(AtomicOptionDuration::new(
      system_time.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
    ))
  }

  /// Loads a value from the atomic system time.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn load(&self, order: Ordering) -> Option<SystemTime> {
    self.0.load(order).map(|val| SystemTime::UNIX_EPOCH + val)
  }

  /// Stores a value into the atomic system time.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn store(&self, system_time: Option<SystemTime>, order: Ordering) {
    self.0.store(
      system_time.map(|val| val.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
      order,
    )
  }

  /// Stores a value into the atomic system time, returning the previous value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn swap(&self, system_time: Option<SystemTime>, order: Ordering) -> Option<SystemTime> {
    self
      .0
      .swap(
        system_time.map(|val| val.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
        order,
      )
      .map(|val| SystemTime::UNIX_EPOCH + val)
  }

  /// Stores a value into the atomic system time if the current value is the same as the `current`
  /// value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn compare_exchange(
    &self,
    current: Option<SystemTime>,
    new: Option<SystemTime>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<SystemTime>, Option<SystemTime>> {
    match self.0.compare_exchange(
      current.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
      new.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
      success,
      failure,
    ) {
      Ok(duration) => Ok(duration.map(|d| SystemTime::UNIX_EPOCH + d)),
      Err(duration) => Err(duration.map(|d| SystemTime::UNIX_EPOCH + d)),
    }
  }

  /// Stores a value into the atomic system time if the current value is the same as the `current`
  /// value.
  ///
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn compare_exchange_weak(
    &self,
    current: Option<SystemTime>,
    new: Option<SystemTime>,
    success: Ordering,
    failure: Ordering,
  ) -> Result<Option<SystemTime>, Option<SystemTime>> {
    match self.0.compare_exchange_weak(
      current.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
      new.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()),
      success,
      failure,
    ) {
      Ok(duration) => Ok(duration.map(|d| SystemTime::UNIX_EPOCH + d)),
      Err(duration) => Err(duration.map(|d| SystemTime::UNIX_EPOCH + d)),
    }
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
  /// # Panics
  ///
  /// If the given `SystemTime` value is earlier than the [`UNIX_EPOCH`](SystemTime::UNIX_EPOCH).
  ///
  /// # Examples
  ///
  /// ```rust
  /// use atomic_time::AtomicOptionSystemTime;
  /// use std::{time::{Duration, SystemTime}, sync::atomic::Ordering};
  ///
  /// let now = SystemTime::now();
  /// let x = AtomicOptionSystemTime::none();
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None), Err(None));
  /// x.store(Some(now), Ordering::SeqCst);
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now)));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now + Duration::from_secs(1))));
  /// assert_eq!(x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |x| Some(x.map(|val| val + Duration::from_secs(1)))), Ok(Some(now + Duration::from_secs(2))));
  /// assert_eq!(x.load(Ordering::SeqCst), Some(now + Duration::from_secs(3)));
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<Option<SystemTime>, Option<SystemTime>>
  where
    F: FnMut(Option<SystemTime>) -> Option<Option<SystemTime>>,
  {
    self
      .0
      .fetch_update(set_order, fetch_order, |duration| {
        f(duration.map(|d| SystemTime::UNIX_EPOCH + d))
          .map(|system_time| system_time.map(|d| d.duration_since(SystemTime::UNIX_EPOCH).unwrap()))
      })
      .map(|duration| duration.map(|d| SystemTime::UNIX_EPOCH + d))
      .map_err(|duration| duration.map(|d| SystemTime::UNIX_EPOCH + d))
  }

  /// Returns `true` if operations on values of this type are lock-free.
  /// If the compiler or the platform doesn't support the necessary
  /// atomic instructions, global locks for every potentially
  /// concurrent atomic operation will be used.
  ///
  /// # Examples
  /// ```
  /// use atomic_time::AtomicOptionSystemTime;
  ///
  /// let is_lock_free = AtomicOptionSystemTime::is_lock_free();
  /// ```
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn is_lock_free() -> bool {
    AtomicOptionDuration::is_lock_free()
  }

  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[cfg_attr(not(tarpaulin), inline(always))]
  pub fn into_inner(self) -> Option<SystemTime> {
    self.0.into_inner().map(|d| SystemTime::UNIX_EPOCH + d)
  }
}

#[cfg(feature = "serde")]
const _: () = {
  use serde::{Deserialize, Serialize};

  impl Serialize for AtomicOptionSystemTime {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
      self.load(Ordering::SeqCst).serialize(serializer)
    }
  }

  impl<'de> Deserialize<'de> for AtomicOptionSystemTime {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
      Ok(Self::new(Option::<SystemTime>::deserialize(deserializer)?))
    }
  }
};

#[cfg(test)]
mod tests {
  use super::*;
  use std::time::Duration;

  #[test]
  fn test_atomic_option_system_time_now() {
    let atomic_time = AtomicOptionSystemTime::now();
    // Check that the time is not None and close to the current time.
    assert!(atomic_time.load(Ordering::SeqCst).is_some());
  }

  #[test]
  fn test_atomic_option_system_time_none() {
    let atomic_time = AtomicOptionSystemTime::none();
    assert_eq!(atomic_time.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_system_time_new_and_load() {
    let now = SystemTime::now();
    let atomic_time = AtomicOptionSystemTime::new(Some(now));
    assert_eq!(atomic_time.load(Ordering::SeqCst), Some(now));
  }

  #[test]
  fn test_atomic_option_system_time_store_and_load() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicOptionSystemTime::new(Some(now));
    atomic_time.store(Some(after_one_sec), Ordering::SeqCst);
    assert_eq!(atomic_time.load(Ordering::SeqCst), Some(after_one_sec));
  }

  #[test]
  fn test_atomic_option_system_time_swap() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicOptionSystemTime::new(Some(now));
    let prev_time = atomic_time.swap(Some(after_one_sec), Ordering::SeqCst);
    assert_eq!(prev_time, Some(now));
    assert_eq!(atomic_time.load(Ordering::SeqCst), Some(after_one_sec));
  }

  #[test]
  fn test_atomic_option_system_time_compare_exchange() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicOptionSystemTime::new(Some(now));
    let result = atomic_time.compare_exchange(
      Some(now),
      Some(after_one_sec),
      Ordering::SeqCst,
      Ordering::SeqCst,
    );
    assert!(result.is_ok());
    assert_eq!(atomic_time.load(Ordering::SeqCst), Some(after_one_sec));
  }

  #[test]
  fn test_atomic_option_system_time_compare_exchange_weak() {
    let now = SystemTime::now();
    let after_one_sec = now + Duration::from_secs(1);
    let atomic_time = AtomicOptionSystemTime::new(Some(now));

    let mut result;
    loop {
      result = atomic_time.compare_exchange_weak(
        Some(now),
        Some(after_one_sec),
        Ordering::SeqCst,
        Ordering::SeqCst,
      );
      if result.is_ok() {
        break;
      }
    }
    assert!(result.is_ok());
    assert_eq!(atomic_time.load(Ordering::SeqCst), Some(after_one_sec));
  }

  #[test]
  fn test_atomic_option_system_time_fetch_update() {
    let now = SystemTime::now();
    let atomic_time = AtomicOptionSystemTime::new(Some(now));

    let result = atomic_time.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |prev| {
      Some(prev.map(|val| val + Duration::from_secs(1)))
    });
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), Some(now));
    assert_eq!(
      atomic_time.load(Ordering::SeqCst),
      Some(now + Duration::from_secs(1))
    );
  }

  #[test]
  fn test_atomic_option_system_time_thread_safety() {
    use std::sync::Arc;
    use std::thread;

    // Fixed starting value + CAS loop = exact final result. The
    // earlier implementation did `load + add + store` and asserted
    // only that the final time was "within 4 seconds of now" — a
    // bound that holds even when every concurrent update was lost.
    let start = SystemTime::now();
    let atomic_time = Arc::new(AtomicOptionSystemTime::new(Some(start)));
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
  fn test_atomic_option_system_time_debug() {
    let atomic_time = AtomicOptionSystemTime::now();
    let debug_str = format!("{:?}", atomic_time);
    assert!(debug_str.contains("AtomicOptionSystemTime"));
  }

  #[test]
  fn test_atomic_option_system_time_default() {
    let atomic_time = AtomicOptionSystemTime::default();
    assert_eq!(atomic_time.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_system_time_from() {
    let now = Some(SystemTime::now());
    let atomic_time = AtomicOptionSystemTime::from(now);
    assert_eq!(atomic_time.load(Ordering::SeqCst), now);
  }

  #[test]
  fn test_atomic_option_system_time_from_none() {
    let atomic_time = AtomicOptionSystemTime::from(None);
    assert_eq!(atomic_time.load(Ordering::SeqCst), None);
  }

  #[test]
  fn test_atomic_option_system_time_into_inner() {
    let now = Some(SystemTime::now());
    let atomic_time = AtomicOptionSystemTime::new(now);
    assert_eq!(atomic_time.into_inner(), now);
  }

  #[test]
  fn test_atomic_option_system_time_into_inner_none() {
    let atomic_time = AtomicOptionSystemTime::none();
    assert_eq!(atomic_time.into_inner(), None);
  }

  #[test]
  fn test_atomic_option_system_time_compare_exchange_failure() {
    let now = Some(SystemTime::now());
    let other = now.map(|t| t + Duration::from_secs(5));
    let atomic_time = AtomicOptionSystemTime::new(now);
    let result = atomic_time.compare_exchange(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[test]
  fn test_atomic_option_system_time_compare_exchange_weak_failure() {
    let now = Some(SystemTime::now());
    let other = now.map(|t| t + Duration::from_secs(5));
    let atomic_time = AtomicOptionSystemTime::new(now);
    let result =
      atomic_time.compare_exchange_weak(other, other, Ordering::SeqCst, Ordering::SeqCst);
    assert!(result.is_err());
  }

  #[test]
  fn test_atomic_option_system_time_fetch_update_failure() {
    let now = Some(SystemTime::now());
    let atomic_time = AtomicOptionSystemTime::new(now);
    let result = atomic_time.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |_| None);
    assert!(result.is_err());
    assert_eq!(result.unwrap_err(), now);
  }

  #[cfg(feature = "serde")]
  #[test]
  fn test_atomic_system_time_serde() {
    use serde::{Deserialize, Serialize};

    #[derive(Serialize, Deserialize)]
    struct Test {
      time: AtomicOptionSystemTime,
    }

    let now = SystemTime::now();
    let test = Test {
      time: AtomicOptionSystemTime::new(Some(now)),
    };
    let serialized = serde_json::to_string(&test).unwrap();
    let deserialized: Test = serde_json::from_str(&serialized).unwrap();
    assert_eq!(deserialized.time.load(Ordering::SeqCst), Some(now));
  }
}
