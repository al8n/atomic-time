use core::{sync::atomic::Ordering, time::Duration as StdDuration};

use atomic::Atomic;

/// Atomic version of [`Duration`](StdDuration)
#[repr(transparent)]
pub struct AtomicDuration(Atomic<Duration>);

impl core::fmt::Debug for AtomicDuration {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    f.debug_tuple("AtomicDuration")
      .field(&self.load(Ordering::SeqCst))
      .finish()
  }
}

impl AtomicDuration {
  /// Creates a new `AtomicDuration` with the given value.
  pub const fn new(duration: StdDuration) -> Self {
    Self(Atomic::new(Duration::from_std(duration)))
  }

  /// Loads [`Duration`](StdDuration) from `AtomicDuration`.
  ///
  /// load takes an [`Ordering`] argument which describes the memory ordering of this operation.
  ///
  /// # Panics
  /// Panics if order is [`Release`](Ordering::Release) or [`AcqRel`](Ordering::AcqRel).
  pub fn load(&self, ordering: Ordering) -> StdDuration {
    self.0.load(ordering).to_std()
  }

  /// Stores a value into the `AtomicDuration`.
  ///
  /// `store` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  ///
  /// # Panics
  ///
  /// Panics if `order` is [`Acquire`](Ordering::Acquire) or [`AcqRel`](Ordering::AcqRel).
  pub fn store(&self, val: StdDuration, ordering: Ordering) {
    self.0.store(Duration::from_std(val), ordering)
  }

  /// Stores a value into the `AtomicDuration`, returning the old value.
  ///
  /// `swap` takes an [`Ordering`] argument which describes the memory ordering
  /// of this operation.
  pub fn swap(&self, val: StdDuration, ordering: Ordering) -> StdDuration {
    self.0.swap(Duration::from_std(val), ordering).to_std()
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
  pub fn compare_exchange_weak(
    &self,
    current: StdDuration,
    new: StdDuration,
    success: Ordering,
    failure: Ordering,
  ) -> Result<StdDuration, StdDuration> {
    self
      .0
      .compare_exchange_weak(
        Duration::from_std(current),
        Duration::from_std(new),
        success,
        failure,
      )
      .map(|d| d.to_std())
      .map_err(|d| d.to_std())
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
  pub fn compare_exchange(
    &self,
    current: StdDuration,
    new: StdDuration,
    success: Ordering,
    failure: Ordering,
  ) -> Result<StdDuration, StdDuration> {
    self
      .0
      .compare_exchange(
        Duration::from_std(current),
        Duration::from_std(new),
        success,
        failure,
      )
      .map(|d| d.to_std())
      .map_err(|d| d.to_std())
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
  pub fn fetch_update<F>(
    &self,
    set_order: Ordering,
    fetch_order: Ordering,
    mut f: F,
  ) -> Result<StdDuration, StdDuration>
  where
    F: FnMut(StdDuration) -> Option<StdDuration>,
  {
    self
      .0
      .fetch_update(set_order, fetch_order, |d| {
        f(d.to_std()).map(Duration::from_std)
      })
      .map(|d| d.to_std())
      .map_err(|d| d.to_std())
  }

  /// Consumes the atomic and returns the contained value.
  ///
  /// This is safe because passing `self` by value guarantees that no other threads are
  /// concurrently accessing the atomic data.
  #[inline]
  pub fn into_inner(self) -> StdDuration {
    self.0.into_inner().to_std()
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
      Ok(Self::new(StdDuration::deserialize(deserializer)?))
    }
  }
};

/// A duration type that does not contain any padding bytes
#[derive(Clone, Copy)]
#[repr(C)]
pub(crate) struct Duration {
  secs_hi: u32,
  secs_lo: u32,
  nanos: u32,
}

const _: fn() = || {
  #[doc(hidden)]
  struct TypeWithoutPadding(
    [u8;
      ::core::mem::size_of::<u32>() + ::core::mem::size_of::<u32>() + ::core::mem::size_of::<u32>()],
  );
  let _ = ::core::mem::transmute::<Duration, TypeWithoutPadding>;
};
const _: fn() = || {
  #[allow(clippy::missing_const_for_fn)]
  #[doc(hidden)]
  fn check() {
    fn assert_impl<T: ::bytemuck::NoUninit>() {}
    assert_impl::<u32>();
  }
};
const _: fn() = || {
  #[allow(clippy::missing_const_for_fn)]
  #[doc(hidden)]
  fn check() {
    fn assert_impl<T: ::bytemuck::NoUninit>() {}
    assert_impl::<u32>();
  }
};
const _: fn() = || {
  #[allow(clippy::missing_const_for_fn)]
  #[doc(hidden)]
  fn check() {
    fn assert_impl<T: ::bytemuck::NoUninit>() {}
    assert_impl::<u32>();
  }
};
unsafe impl ::bytemuck::NoUninit for Duration {}

impl Duration {
  pub const fn from_std(d: StdDuration) -> Self {
    let nanos = d.subsec_nanos();
    let secs = d.as_secs();
    Self {
      secs_hi: (secs >> 32) as u32,
      secs_lo: secs as u32,
      nanos,
    }
  }

  pub const fn to_std(self) -> StdDuration {
    let secs = (self.secs_hi as u64) << 32 | self.secs_lo as u64;
    StdDuration::new(secs, self.nanos)
  }

  pub const fn into_bytes(self) -> [u8; 12] {
    let secs_hi = self.secs_hi.to_be_bytes();
    let secs_lo = self.secs_lo.to_be_bytes();
    let nanos = self.nanos.to_be_bytes();
    [
      secs_hi[0], secs_hi[1], secs_hi[2], secs_hi[3], secs_lo[0], secs_lo[1], secs_lo[2],
      secs_lo[3], nanos[0], nanos[1], nanos[2], nanos[3],
    ]
  }

  pub const fn from_bytes(bytes: [u8; 12]) -> Self {
    let secs_hi = [bytes[0], bytes[1], bytes[2], bytes[3]];
    let secs_lo = [bytes[4], bytes[5], bytes[6], bytes[7]];
    let nanos = [bytes[8], bytes[9], bytes[10], bytes[11]];

    Self {
      secs_hi: u32::from_be_bytes(secs_hi),
      secs_lo: u32::from_be_bytes(secs_lo),
      nanos: u32::from_be_bytes(nanos),
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use core::{sync::atomic::Ordering, time::Duration};

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
}
