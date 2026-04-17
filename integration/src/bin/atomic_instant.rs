use atomic_time::AtomicInstant;
use core::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

fn run() {
  let start = Instant::now();
  let atomic_time = Arc::new(AtomicInstant::new(start));
  let mut handles = vec![];

  for _ in 0..4 {
    let atomic_clone = atomic_time.clone();
    let handle = thread::spawn(move || {
      atomic_clone
        .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
          Some(current + Duration::from_secs(1))
        })
        .unwrap();
    });
    handles.push(handle);
  }

  for handle in handles {
    handle.join().unwrap();
  }

  assert_eq!(
    atomic_time.load(Ordering::SeqCst),
    start + Duration::from_secs(4),
    "4 CAS increments of 1 second each should yield exactly start + 4s"
  );
}

fn main() {
  run();
}

#[cfg(test)]
mod tests {
  #[test]
  fn atomic_instant_cas_increments() {
    super::run();
  }
}
