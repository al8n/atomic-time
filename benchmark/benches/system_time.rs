use std::{
  sync::{atomic::Ordering, Arc},
  time::{Duration, SystemTime},
};

use arc_swap::ArcSwap;
use atomic_time::{AtomicOptionSystemTime, AtomicSystemTime};
use atomic_time_benchmark::{bg_threads, join_all, THREADS};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn single_thread(c: &mut Criterion) {
  let mut g = c.benchmark_group("system_time/single_thread");

  let now = SystemTime::now();
  let next = now + Duration::from_secs(1);

  let v = AtomicSystemTime::new(now);
  g.bench_function("AtomicSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  g.bench_function("AtomicSystemTime/store", |b| {
    b.iter(|| v.store(black_box(next), Ordering::Release))
  });

  let v = AtomicOptionSystemTime::new(Some(now));
  g.bench_function("AtomicOptionSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  g.bench_function("AtomicOptionSystemTime/store", |b| {
    b.iter(|| v.store(black_box(Some(next)), Ordering::Release))
  });

  let sw = ArcSwap::new(Arc::new(now));
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  g.bench_function("ArcSwap/store", |b| {
    b.iter(|| sw.store(Arc::new(black_box(next))))
  });

  let pl = parking_lot::RwLock::new(now);
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  g.bench_function("parking_lot::RwLock/write", |b| {
    b.iter(|| *pl.write() = black_box(next))
  });

  let sr = std::sync::RwLock::new(now);
  g.bench_function("std::sync::RwLock/read", |b| {
    b.iter(|| black_box(*sr.read().unwrap()))
  });
  g.bench_function("std::sync::RwLock/write", |b| {
    b.iter(|| *sr.write().unwrap() = black_box(next))
  });

  g.finish();
}

fn contended_read(c: &mut Criterion) {
  let mut g = c.benchmark_group("system_time/contended_read");

  let now = SystemTime::now();

  let v = Arc::new(AtomicSystemTime::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { black_box(v.load(Ordering::Acquire)); }
  });
  g.bench_function("AtomicSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionSystemTime::new(Some(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { black_box(v.load(Ordering::Acquire)); }
  });
  g.bench_function("AtomicOptionSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { black_box(sw.load()); }
  });
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { black_box(*pl.read()); }
  });
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let sr = sr.clone();
    move || { black_box(*sr.read().unwrap()); }
  });
  g.bench_function("std::sync::RwLock/read", |b| {
    b.iter(|| black_box(*sr.read().unwrap()))
  });
  join_all(stop, handles);

  g.finish();
}

// NOTE: this group was previously called `contended_write`, but it
// actually measures *load* latency on the main thread while background
// threads perform writes. Renamed to `load_under_write_contention` so
// the benchmark ID matches the measured operation.
fn load_under_write_contention(c: &mut Criterion) {
  let mut g = c.benchmark_group("system_time/load_under_write_contention");

  let now = SystemTime::now();
  let next = now + Duration::from_secs(1);

  let v = Arc::new(AtomicSystemTime::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(next, Ordering::Release); }
  });
  g.bench_function("AtomicSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionSystemTime::new(Some(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(Some(next), Ordering::Release); }
  });
  g.bench_function("AtomicOptionSystemTime/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { sw.store(Arc::new(next)); }
  });
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { *pl.write() = next; }
  });
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let sr = sr.clone();
    move || { *sr.write().unwrap() = next; }
  });
  g.bench_function("std::sync::RwLock/read", |b| {
    b.iter(|| black_box(*sr.read().unwrap()))
  });
  join_all(stop, handles);

  g.finish();
}

// Real write-side benchmark: measures store/swap latency on the main
// thread while background threads also write.
fn contended_store(c: &mut Criterion) {
  let mut g = c.benchmark_group("system_time/contended_store");

  let now = SystemTime::now();
  let next = now + Duration::from_secs(1);

  let v = Arc::new(AtomicSystemTime::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(next, Ordering::Release); }
  });
  g.bench_function("AtomicSystemTime/store", |b| {
    b.iter(|| v.store(black_box(next), Ordering::Release))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicSystemTime::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(next, Ordering::Release); }
  });
  g.bench_function("AtomicSystemTime/swap", |b| {
    b.iter(|| black_box(v.swap(black_box(next), Ordering::AcqRel)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionSystemTime::new(Some(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(Some(next), Ordering::Release); }
  });
  g.bench_function("AtomicOptionSystemTime/store", |b| {
    b.iter(|| v.store(black_box(Some(next)), Ordering::Release))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(now)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { sw.store(Arc::new(next)); }
  });
  g.bench_function("ArcSwap/store", |b| {
    b.iter(|| sw.store(Arc::new(black_box(next))))
  });
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { *pl.write() = next; }
  });
  g.bench_function("parking_lot::RwLock/write", |b| {
    b.iter(|| *pl.write() = black_box(next))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(now));
  let (stop, handles) = bg_threads(THREADS, {
    let sr = sr.clone();
    move || { *sr.write().unwrap() = next; }
  });
  g.bench_function("std::sync::RwLock/write", |b| {
    b.iter(|| *sr.write().unwrap() = black_box(next))
  });
  join_all(stop, handles);

  g.finish();
}

criterion_group!(
  benches,
  single_thread,
  contended_read,
  load_under_write_contention,
  contended_store
);
criterion_main!(benches);
