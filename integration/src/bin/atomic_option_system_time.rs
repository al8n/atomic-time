use atomic_time::AtomicOptionSystemTime;
use core::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, SystemTime};

fn run() {
  let start = SystemTime::now();
  let atomic_time = Arc::new(AtomicOptionSystemTime::new(Some(start)));
  let mut handles = vec![];

  for _ in 0..4 {
    let atomic_clone = Arc::clone(&atomic_time);
    let handle = thread::spawn(move || {
      atomic_clone
        .fetch_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
          current.map(|t| Some(t + Duration::from_secs(1)))
        })
        .expect("atomic is always Some in this test");
    });
    handles.push(handle);
  }

  for handle in handles {
    handle.join().unwrap();
  }

  assert_eq!(
    atomic_time.load(Ordering::SeqCst),
    Some(start + Duration::from_secs(4)),
    "4 CAS increments of 1 second each should yield exactly start + 4s"
  );
}

fn main() {
  run();
}

#[cfg(test)]
mod tests {
  #[test]
  fn atomic_option_system_time_cas_increments() {
    super::run();
  }
}
