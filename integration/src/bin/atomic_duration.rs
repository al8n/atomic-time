use atomic_time::AtomicDuration;
use core::{sync::atomic::Ordering, time::Duration};

fn main() {
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
          match atomic_clone.compare_exchange_weak(current, new, Ordering::SeqCst, Ordering::SeqCst)
          {
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
