use std::{
  sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
  },
  thread,
};

pub const THREADS: usize = 4;

pub fn bg_threads(
  n: usize,
  f: impl Fn() + Send + Sync + 'static,
) -> (Arc<AtomicBool>, Vec<thread::JoinHandle<()>>) {
  let stop = Arc::new(AtomicBool::new(false));
  let f = Arc::new(f);
  let handles = (0..n)
    .map(|_| {
      let stop = stop.clone();
      let f = f.clone();
      thread::spawn(move || {
        while !stop.load(Ordering::Relaxed) {
          f();
        }
      })
    })
    .collect();
  (stop, handles)
}

pub fn join_all(stop: Arc<AtomicBool>, handles: Vec<thread::JoinHandle<()>>) {
  stop.store(true, Ordering::Relaxed);
  for h in handles {
    h.join().unwrap();
  }
}
