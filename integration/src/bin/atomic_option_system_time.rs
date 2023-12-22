use atomic_time::AtomicOptionSystemTime;
use core::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, SystemTime};

fn main() {
  let atomic_time = Arc::new(AtomicOptionSystemTime::now());
  let mut handles = vec![];

  // Spawn multiple threads to update the time
  for _ in 0..4 {
    let atomic_clone = Arc::clone(&atomic_time);
    let handle = thread::spawn(move || {
      let current = atomic_clone.load(Ordering::SeqCst);
      if let Some(current_time) = current {
        // Adding 1 second to the current time
        let new_time = current_time + Duration::from_secs(1);
        atomic_clone.store(Some(new_time), Ordering::SeqCst);
      }
    });
    handles.push(handle);
  }

  // Wait for all threads to complete
  for handle in handles {
    handle.join().unwrap();
  }

  // Verify that the time has been updated
  if let Some(updated_time) = atomic_time.load(Ordering::SeqCst) {
    assert!(updated_time > SystemTime::now() - Duration::from_secs(4));
  } else {
    panic!("AtomicOptionSystemTime should not be None");
  }
}
