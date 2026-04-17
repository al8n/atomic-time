use atomic_time::AtomicOptionDuration;
use core::sync::atomic::Ordering;
use core::time::Duration as StdDuration;
use std::sync::Arc;
use std::thread;

fn run() {
  let atomic_duration = Arc::new(AtomicOptionDuration::new(Some(StdDuration::from_secs(0))));
  let mut handles = vec![];

  for _ in 0..10 {
    let atomic_clone = Arc::clone(&atomic_duration);
    let handle = thread::spawn(move || {
      for _ in 0..100 {
        loop {
          let current = atomic_clone.load(Ordering::SeqCst);
          let new_duration = current
            .map(|d| d + StdDuration::from_millis(1))
            .or(Some(StdDuration::from_millis(1)));
          match atomic_clone.compare_exchange_weak(
            current,
            new_duration,
            Ordering::SeqCst,
            Ordering::SeqCst,
          ) {
            Ok(_) => break,
            Err(_) => continue,
          }
        }
      }
    });
    handles.push(handle);
  }

  for handle in handles {
    handle.join().unwrap();
  }

  let expected_duration = Some(StdDuration::from_millis(10 * 100));
  assert_eq!(atomic_duration.load(Ordering::SeqCst), expected_duration);
}

fn main() {
  run();
}

#[cfg(test)]
mod tests {
  #[test]
  fn atomic_option_duration_cas_increments() {
    super::run();
  }
}
