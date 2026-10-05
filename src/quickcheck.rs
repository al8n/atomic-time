use core::sync::atomic::Ordering;
use std::{
  boxed::Box,
  time::{Duration, SystemTime},
};

use ::quickcheck::{Arbitrary, Gen};

use crate::{AtomicDuration, AtomicOptionDuration, AtomicOptionSystemTime, AtomicSystemTime};

fn system_time_from_parts((seconds, nanoseconds): (u32, u32)) -> SystemTime {
  let duration = Duration::new(
    u64::from(seconds.min(i32::MAX as u32)),
    nanoseconds % 1_000_000_000,
  );
  SystemTime::UNIX_EPOCH
    .checked_add(duration)
    .unwrap_or(SystemTime::UNIX_EPOCH)
}

fn system_time_from_duration(duration: Duration) -> SystemTime {
  SystemTime::UNIX_EPOCH
    .checked_add(duration)
    .unwrap_or(SystemTime::UNIX_EPOCH)
}

fn duration_since_epoch(system_time: SystemTime) -> Duration {
  system_time
    .duration_since(SystemTime::UNIX_EPOCH)
    .unwrap_or(Duration::ZERO)
}

impl Clone for AtomicDuration {
  /// Creates an atomic snapshot of this value with sequentially consistent
  /// ordering.
  ///
  /// If another thread writes concurrently, the clone contains the value
  /// observed at this load's atomic linearization point.
  #[inline(always)]
  fn clone(&self) -> Self {
    Self::new(self.load(Ordering::SeqCst))
  }
}

impl Clone for AtomicOptionDuration {
  /// Creates an atomic snapshot of this value with sequentially consistent
  /// ordering.
  ///
  /// If another thread writes concurrently, the clone contains the value
  /// observed at this load's atomic linearization point.
  #[inline(always)]
  fn clone(&self) -> Self {
    Self::new(self.load(Ordering::SeqCst))
  }
}

impl Clone for AtomicSystemTime {
  /// Creates an atomic snapshot of this value with sequentially consistent
  /// ordering.
  ///
  /// If another thread writes concurrently, the clone contains the value
  /// observed at this load's atomic linearization point.
  #[inline(always)]
  fn clone(&self) -> Self {
    Self::new(self.load(Ordering::SeqCst))
  }
}

impl Clone for AtomicOptionSystemTime {
  /// Creates an atomic snapshot of this value with sequentially consistent
  /// ordering.
  ///
  /// If another thread writes concurrently, the clone contains the value
  /// observed at this load's atomic linearization point.
  #[inline(always)]
  fn clone(&self) -> Self {
    Self::new(self.load(Ordering::SeqCst))
  }
}

impl Arbitrary for AtomicDuration {
  fn arbitrary(g: &mut Gen) -> Self {
    Self::new(Duration::arbitrary(g))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    Box::new(self.load(Ordering::SeqCst).shrink().map(Self::new))
  }
}

impl Arbitrary for AtomicOptionDuration {
  fn arbitrary(g: &mut Gen) -> Self {
    Self::new(Option::<Duration>::arbitrary(g))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    Box::new(self.load(Ordering::SeqCst).shrink().map(Self::new))
  }
}

impl Arbitrary for AtomicSystemTime {
  fn arbitrary(g: &mut Gen) -> Self {
    Self::new(system_time_from_parts(<(u32, u32)>::arbitrary(g)))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    Box::new(
      duration_since_epoch(self.load(Ordering::SeqCst))
        .shrink()
        .map(|duration| Self::new(system_time_from_duration(duration))),
    )
  }
}

impl Arbitrary for AtomicOptionSystemTime {
  fn arbitrary(g: &mut Gen) -> Self {
    Self::new(Option::<(u32, u32)>::arbitrary(g).map(system_time_from_parts))
  }

  fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
    Box::new(
      self
        .load(Ordering::SeqCst)
        .map(duration_since_epoch)
        .shrink()
        .map(|duration| Self::new(duration.map(system_time_from_duration))),
    )
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn arbitrary_values_can_be_loaded() {
    let mut generator = Gen::new(32);

    let duration = AtomicDuration::arbitrary(&mut generator);
    let _ = duration.load(Ordering::SeqCst);

    let option_duration = AtomicOptionDuration::arbitrary(&mut generator);
    let _ = option_duration.load(Ordering::SeqCst);

    let system_time = AtomicSystemTime::arbitrary(&mut generator);
    assert!(system_time
      .load(Ordering::SeqCst)
      .duration_since(SystemTime::UNIX_EPOCH)
      .is_ok());

    let option_system_time = AtomicOptionSystemTime::arbitrary(&mut generator);
    assert!(option_system_time
      .load(Ordering::SeqCst)
      .is_none_or(|value| value.duration_since(SystemTime::UNIX_EPOCH).is_ok()));
  }

  #[test]
  fn clone_takes_a_snapshot() {
    let duration = AtomicDuration::new(Duration::from_secs(1));
    let duration_clone = duration.clone();
    duration.store(Duration::from_secs(2), Ordering::SeqCst);
    assert_eq!(
      duration_clone.load(Ordering::SeqCst),
      Duration::from_secs(1)
    );

    let option_duration = AtomicOptionDuration::new(Some(Duration::from_secs(1)));
    let option_duration_clone = option_duration.clone();
    option_duration.store(None, Ordering::SeqCst);
    assert_eq!(
      option_duration_clone.load(Ordering::SeqCst),
      Some(Duration::from_secs(1))
    );

    let system_time = AtomicSystemTime::new(SystemTime::UNIX_EPOCH);
    let system_time_clone = system_time.clone();
    system_time.store(
      SystemTime::UNIX_EPOCH + Duration::from_secs(1),
      Ordering::SeqCst,
    );
    assert_eq!(
      system_time_clone.load(Ordering::SeqCst),
      SystemTime::UNIX_EPOCH
    );

    let option_system_time = AtomicOptionSystemTime::new(Some(SystemTime::UNIX_EPOCH));
    let option_system_time_clone = option_system_time.clone();
    option_system_time.store(None, Ordering::SeqCst);
    assert_eq!(
      option_system_time_clone.load(Ordering::SeqCst),
      Some(SystemTime::UNIX_EPOCH)
    );
  }

  #[test]
  fn shrunk_system_times_remain_valid() {
    let system_time = AtomicSystemTime::new(SystemTime::UNIX_EPOCH + Duration::from_secs(10));
    for value in system_time.shrink().take(64) {
      assert!(value
        .load(Ordering::SeqCst)
        .duration_since(SystemTime::UNIX_EPOCH)
        .is_ok());
    }

    let none = AtomicOptionSystemTime::none();
    assert!(none.shrink().next().is_none());

    let some = AtomicOptionSystemTime::new(Some(SystemTime::UNIX_EPOCH + Duration::from_secs(10)));
    for value in some.shrink().take(64) {
      assert!(value
        .load(Ordering::SeqCst)
        .is_none_or(|time| time.duration_since(SystemTime::UNIX_EPOCH).is_ok()));
    }
  }
}
