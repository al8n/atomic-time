use atomic_time::AtomicOptionDuration;
use core::sync::atomic::Ordering;
use core::time::Duration as StdDuration;
use std::sync::Arc;
use std::thread;

fn main() {
  let atomic_duration = Arc::new(AtomicOptionDuration::new(Some(StdDuration::from_secs(0))));
  let mut handles = vec![];

  // Spawn multiple threads to increment the duration
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
  let expected_duration = Some(StdDuration::from_millis(10 * 100));
  assert_eq!(atomic_duration.load(Ordering::SeqCst), expected_duration);
}
