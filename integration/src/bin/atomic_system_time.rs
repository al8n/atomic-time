use atomic_time::AtomicSystemTime;
use core::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, SystemTime};

fn main() {
  let atomic_time = Arc::new(AtomicSystemTime::now());
  let mut handles = vec![];

  for _ in 0..4 {
    let atomic_clone = atomic_time.clone();
    let handle = thread::spawn(move || {
      let current = atomic_clone.load(Ordering::SeqCst);
      let new = current + Duration::from_secs(1);
      atomic_clone.store(new, Ordering::SeqCst);
    });
    handles.push(handle);
  }

  for handle in handles {
    handle.join().unwrap();
  }

  // This checks that the time has advanced, but it's not precise about how much,
  // due to the non-deterministic nature of thread execution order and timing.
  assert!(atomic_time.load(Ordering::SeqCst) > SystemTime::now());
}
