use std::{
  sync::{atomic::Ordering, Arc},
  time::Duration,
};

use arc_swap::ArcSwap;
use atomic_time::{AtomicDuration, AtomicOptionDuration};
use atomic_time_benchmark::{bg_threads, join_all, THREADS};
use criterion::{black_box, criterion_group, criterion_main, Criterion};

const INIT: Duration = Duration::from_nanos(5000);
const NEXT: Duration = Duration::from_nanos(10000);

fn single_thread(c: &mut Criterion) {
  let mut g = c.benchmark_group("duration/single_thread");

  let v = AtomicDuration::new(INIT);
  g.bench_function("AtomicDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  g.bench_function("AtomicDuration/store", |b| {
    b.iter(|| v.store(black_box(NEXT), Ordering::Release))
  });

  let v = AtomicOptionDuration::new(Some(INIT));
  g.bench_function("AtomicOptionDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  g.bench_function("AtomicOptionDuration/store", |b| {
    b.iter(|| v.store(black_box(Some(NEXT)), Ordering::Release))
  });

  let sw = ArcSwap::new(Arc::new(INIT));
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  g.bench_function("ArcSwap/store", |b| {
    b.iter(|| sw.store(Arc::new(black_box(NEXT))))
  });

  let pl = parking_lot::RwLock::new(INIT);
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  g.bench_function("parking_lot::RwLock/write", |b| {
    b.iter(|| *pl.write() = black_box(NEXT))
  });

  let sr = std::sync::RwLock::new(INIT);
  g.bench_function("std::sync::RwLock/read", |b| {
    b.iter(|| black_box(*sr.read().unwrap()))
  });
  g.bench_function("std::sync::RwLock/write", |b| {
    b.iter(|| *sr.write().unwrap() = black_box(NEXT))
  });

  g.finish();
}

fn contended_read(c: &mut Criterion) {
  let mut g = c.benchmark_group("duration/contended_read");

  let v = Arc::new(AtomicDuration::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { black_box(v.load(Ordering::Acquire)); }
  });
  g.bench_function("AtomicDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionDuration::new(Some(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { black_box(v.load(Ordering::Acquire)); }
  });
  g.bench_function("AtomicOptionDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { black_box(sw.load()); }
  });
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { black_box(*pl.read()); }
  });
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(INIT));
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
  let mut g = c.benchmark_group("duration/load_under_write_contention");

  let v = Arc::new(AtomicDuration::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(NEXT, Ordering::Release); }
  });
  g.bench_function("AtomicDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionDuration::new(Some(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(Some(NEXT), Ordering::Release); }
  });
  g.bench_function("AtomicOptionDuration/load", |b| {
    b.iter(|| black_box(v.load(Ordering::Acquire)))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { sw.store(Arc::new(NEXT)); }
  });
  g.bench_function("ArcSwap/load", |b| b.iter(|| black_box(sw.load())));
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { *pl.write() = NEXT; }
  });
  g.bench_function("parking_lot::RwLock/read", |b| {
    b.iter(|| black_box(*pl.read()))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let sr = sr.clone();
    move || { *sr.write().unwrap() = NEXT; }
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
  let mut g = c.benchmark_group("duration/contended_store");

  let v = Arc::new(AtomicDuration::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(NEXT, Ordering::Release); }
  });
  g.bench_function("AtomicDuration/store", |b| {
    b.iter(|| v.store(black_box(NEXT), Ordering::Release))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicDuration::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(NEXT, Ordering::Release); }
  });
  g.bench_function("AtomicDuration/swap", |b| {
    b.iter(|| black_box(v.swap(black_box(NEXT), Ordering::AcqRel)))
  });
  join_all(stop, handles);

  let v = Arc::new(AtomicOptionDuration::new(Some(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let v = v.clone();
    move || { v.store(Some(NEXT), Ordering::Release); }
  });
  g.bench_function("AtomicOptionDuration/store", |b| {
    b.iter(|| v.store(black_box(Some(NEXT)), Ordering::Release))
  });
  join_all(stop, handles);

  let sw = Arc::new(ArcSwap::new(Arc::new(INIT)));
  let (stop, handles) = bg_threads(THREADS, {
    let sw = sw.clone();
    move || { sw.store(Arc::new(NEXT)); }
  });
  g.bench_function("ArcSwap/store", |b| {
    b.iter(|| sw.store(Arc::new(black_box(NEXT))))
  });
  join_all(stop, handles);

  let pl = Arc::new(parking_lot::RwLock::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let pl = pl.clone();
    move || { *pl.write() = NEXT; }
  });
  g.bench_function("parking_lot::RwLock/write", |b| {
    b.iter(|| *pl.write() = black_box(NEXT))
  });
  join_all(stop, handles);

  let sr = Arc::new(std::sync::RwLock::new(INIT));
  let (stop, handles) = bg_threads(THREADS, {
    let sr = sr.clone();
    move || { *sr.write().unwrap() = NEXT; }
  });
  g.bench_function("std::sync::RwLock/write", |b| {
    b.iter(|| *sr.write().unwrap() = black_box(NEXT))
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
