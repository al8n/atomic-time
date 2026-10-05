use core::time::Duration;

use ::arbitrary::{Arbitrary, Result, Unstructured};

use crate::{AtomicDuration, AtomicOptionDuration};

#[cfg(feature = "std")]
use crate::{AtomicOptionSystemTime, AtomicSystemTime};
#[cfg(feature = "std")]
use std::time::SystemTime;

impl<'a> Arbitrary<'a> for AtomicDuration {
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    <Duration as Arbitrary>::arbitrary(u).map(Self::new)
  }

  fn size_hint(depth: usize) -> (usize, Option<usize>) {
    <Duration as Arbitrary>::size_hint(depth)
  }
}

impl<'a> Arbitrary<'a> for AtomicOptionDuration {
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    <Option<Duration> as Arbitrary>::arbitrary(u).map(Self::new)
  }

  fn size_hint(depth: usize) -> (usize, Option<usize>) {
    <Option<Duration> as Arbitrary>::size_hint(depth)
  }
}

#[cfg(feature = "std")]
fn system_time_from_parts((seconds, nanoseconds): (u32, u32)) -> SystemTime {
  let duration = Duration::new(
    u64::from(seconds.min(i32::MAX as u32)),
    nanoseconds % 1_000_000_000,
  );
  SystemTime::UNIX_EPOCH
    .checked_add(duration)
    .unwrap_or(SystemTime::UNIX_EPOCH)
}

#[cfg(feature = "std")]
impl<'a> Arbitrary<'a> for AtomicSystemTime {
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    <(u32, u32) as Arbitrary>::arbitrary(u)
      .map(system_time_from_parts)
      .map(Self::new)
  }

  fn size_hint(depth: usize) -> (usize, Option<usize>) {
    <(u32, u32) as Arbitrary>::size_hint(depth)
  }
}

#[cfg(feature = "std")]
impl<'a> Arbitrary<'a> for AtomicOptionSystemTime {
  fn arbitrary(u: &mut Unstructured<'a>) -> Result<Self> {
    <Option<(u32, u32)> as Arbitrary>::arbitrary(u)
      .map(|parts| Self::new(parts.map(system_time_from_parts)))
  }

  fn size_hint(depth: usize) -> (usize, Option<usize>) {
    <Option<(u32, u32)> as Arbitrary>::size_hint(depth)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use core::sync::atomic::Ordering;

  #[test]
  fn duration_types_are_deterministic_and_delegate_size_hints() {
    let input = [0xff; 32];
    let mut first_input = Unstructured::new(&input);
    let first = AtomicDuration::arbitrary(&mut first_input).unwrap();
    let mut second_input = Unstructured::new(&input);
    let second = AtomicDuration::arbitrary(&mut second_input).unwrap();

    assert_eq!(first.load(Ordering::SeqCst), second.load(Ordering::SeqCst));
    assert!(first_input.len() < input.len());
    assert_eq!(
      <AtomicDuration as Arbitrary>::size_hint(0),
      <Duration as Arbitrary>::size_hint(0)
    );
    assert_eq!(
      <AtomicOptionDuration as Arbitrary>::size_hint(0),
      <Option<Duration> as Arbitrary>::size_hint(0)
    );
  }

  #[test]
  fn duration_types_handle_none_some_and_extreme_input() {
    let mut none_input = Unstructured::new(&[0]);
    let none = AtomicOptionDuration::arbitrary(&mut none_input).unwrap();
    assert_eq!(none.load(Ordering::SeqCst), None);

    let mut some_input = Unstructured::new(&[1; 32]);
    let some = AtomicOptionDuration::arbitrary(&mut some_input).unwrap();
    assert!(some.load(Ordering::SeqCst).is_some());

    let mut extreme_duration_input = Unstructured::new(&[0xff; 32]);
    assert!(AtomicDuration::arbitrary(&mut extreme_duration_input).is_ok());
    let mut extreme_option_input = Unstructured::new(&[0xff; 32]);
    assert!(AtomicOptionDuration::arbitrary(&mut extreme_option_input).is_ok());
  }

  #[cfg(feature = "std")]
  #[test]
  fn system_time_types_are_deterministic_and_after_epoch() {
    let input = [0xff; 32];
    let mut first_input = Unstructured::new(&input);
    let first = AtomicSystemTime::arbitrary(&mut first_input).unwrap();
    let mut second_input = Unstructured::new(&input);
    let second = AtomicSystemTime::arbitrary(&mut second_input).unwrap();

    let first = first.load(Ordering::SeqCst);
    assert_eq!(first, second.load(Ordering::SeqCst));
    assert!(first.duration_since(SystemTime::UNIX_EPOCH).is_ok());
    assert!(first_input.len() < input.len());
    assert_eq!(
      <AtomicSystemTime as Arbitrary>::size_hint(0),
      <(u32, u32) as Arbitrary>::size_hint(0)
    );
    assert_eq!(
      <AtomicOptionSystemTime as Arbitrary>::size_hint(0),
      <Option<(u32, u32)> as Arbitrary>::size_hint(0)
    );
  }

  #[cfg(feature = "std")]
  #[test]
  fn option_system_time_preserves_none_and_some() {
    let mut none_input = Unstructured::new(&[0]);
    let none = AtomicOptionSystemTime::arbitrary(&mut none_input).unwrap();
    assert_eq!(none.load(Ordering::SeqCst), None);

    let mut some_input = Unstructured::new(&[1; 32]);
    let some = AtomicOptionSystemTime::arbitrary(&mut some_input).unwrap();
    assert!(some.load(Ordering::SeqCst).is_some());

    let mut extreme_input = Unstructured::new(&[0xff; 32]);
    let extreme = AtomicSystemTime::arbitrary(&mut extreme_input).unwrap();
    assert!(extreme
      .load(Ordering::SeqCst)
      .duration_since(SystemTime::UNIX_EPOCH)
      .is_ok());

    let mut extreme_option_input = Unstructured::new(&[0xff; 32]);
    let extreme_option = AtomicOptionSystemTime::arbitrary(&mut extreme_option_input).unwrap();
    assert!(extreme_option
      .load(Ordering::SeqCst)
      .is_none_or(|value| value.duration_since(SystemTime::UNIX_EPOCH).is_ok()));
  }
}
