use core::time::Duration;
use std::time::SystemTime;

use ::proptest::{
  arbitrary::{any, Arbitrary},
  strategy::{BoxedStrategy, Just, Strategy},
};

use crate::{AtomicDuration, AtomicOptionDuration, AtomicOptionSystemTime, AtomicSystemTime};

fn duration_strategy() -> BoxedStrategy<Duration> {
  (any::<u64>(), 0..1_000_000_000u32)
    .prop_map(|(seconds, nanoseconds)| Duration::new(seconds, nanoseconds))
    .boxed()
}

fn option_duration_strategy() -> BoxedStrategy<Option<Duration>> {
  ::proptest::prop_oneof![Just(None), duration_strategy().prop_map(Some),].boxed()
}

fn system_time_from_duration(duration: Duration) -> SystemTime {
  SystemTime::UNIX_EPOCH
    .checked_add(duration)
    .unwrap_or(SystemTime::UNIX_EPOCH)
}

fn system_time_strategy() -> BoxedStrategy<SystemTime> {
  (0..=i32::MAX as u64, 0..1_000_000_000u32)
    .prop_map(|(seconds, nanoseconds)| {
      system_time_from_duration(Duration::new(seconds, nanoseconds))
    })
    .boxed()
}

fn option_system_time_strategy() -> BoxedStrategy<Option<SystemTime>> {
  ::proptest::prop_oneof![Just(None), system_time_strategy().prop_map(Some),].boxed()
}

impl Arbitrary for AtomicDuration {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
    duration_strategy().prop_map(Self::new).boxed()
  }
}

impl Arbitrary for AtomicOptionDuration {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
    option_duration_strategy().prop_map(Self::new).boxed()
  }
}

impl Arbitrary for AtomicSystemTime {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
    system_time_strategy().prop_map(Self::new).boxed()
  }
}

impl Arbitrary for AtomicOptionSystemTime {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_: Self::Parameters) -> Self::Strategy {
    option_system_time_strategy().prop_map(Self::new).boxed()
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use core::sync::atomic::Ordering;
  use std::cell::Cell;

  use ::proptest::{strategy::ValueTree, test_runner::TestRunner};

  #[test]
  fn strategies_generate_readable_values() {
    let mut runner = TestRunner::default();

    let duration = <AtomicDuration as Arbitrary>::arbitrary()
      .new_tree(&mut runner)
      .unwrap()
      .current();
    let _ = duration.load(Ordering::SeqCst);

    let option_duration = <AtomicOptionDuration as Arbitrary>::arbitrary()
      .new_tree(&mut runner)
      .unwrap()
      .current();
    let _ = option_duration.load(Ordering::SeqCst);

    let system_time = <AtomicSystemTime as Arbitrary>::arbitrary()
      .new_tree(&mut runner)
      .unwrap()
      .current();
    assert!(system_time
      .load(Ordering::SeqCst)
      .duration_since(SystemTime::UNIX_EPOCH)
      .is_ok());

    let option_system_time = <AtomicOptionSystemTime as Arbitrary>::arbitrary()
      .new_tree(&mut runner)
      .unwrap()
      .current();
    assert!(option_system_time
      .load(Ordering::SeqCst)
      .is_none_or(|value| value.duration_since(SystemTime::UNIX_EPOCH).is_ok()));
  }

  #[test]
  fn option_strategies_cover_none_and_some_without_panicking() {
    let duration_none = Cell::new(false);
    let duration_some = Cell::new(false);
    let duration_strategy = <AtomicOptionDuration as Arbitrary>::arbitrary();
    TestRunner::default()
      .run(&duration_strategy, |value| {
        match value.load(Ordering::SeqCst) {
          None => duration_none.set(true),
          Some(_) => duration_some.set(true),
        }
        Ok(())
      })
      .unwrap();
    assert!(duration_none.get());
    assert!(duration_some.get());

    let system_time_none = Cell::new(false);
    let system_time_some = Cell::new(false);
    let system_time_strategy = <AtomicOptionSystemTime as Arbitrary>::arbitrary();
    TestRunner::default()
      .run(&system_time_strategy, |value| {
        match value.load(Ordering::SeqCst) {
          None => system_time_none.set(true),
          Some(time) => {
            system_time_some.set(true);
            assert!(time.duration_since(SystemTime::UNIX_EPOCH).is_ok());
          }
        }
        Ok(())
      })
      .unwrap();
    assert!(system_time_none.get());
    assert!(system_time_some.get());
  }
}
