# 0.2.1

BUG FIXES

- **`decode_duration` and `decode_option_duration` no longer panic on
  non-canonical input.** Previously, `decode_duration(u128::MAX)` and
  `decode_option_duration(u128::MAX)` called `Duration::new` with
  out-of-range nanoseconds, which panicked when the carry overflowed
  the seconds field. The decoders now normalize the nanosecond count
  and saturate at `Duration::MAX` instead.
- **`decode_instant_from_duration` no longer panics on extreme
  `Duration` values.** Decoding a Duration far exceeding the platform's
  `Instant` range (e.g. `Duration::new(u64::MAX, 999_999_999)`) caused
  `instant_now + delta` to overflow and panic — including through the
  serde `Deserialize` impls for `AtomicInstant` and
  `AtomicOptionInstant`, where a malformed JSON payload would crash
  the process. The function now uses `Instant::checked_add` /
  `checked_sub` and saturates at `instant_now` on overflow.
- **Thread-safety tests now use CAS (`fetch_update`) instead of
  non-atomic load+store**, and assert exact final values. The previous
  tests could silently lose concurrent updates and still pass because
  their assertions were too loose.
- **Integration test suite now actually runs.** The six binaries under
  `integration/src/bin/` had `fn main()` with assertions but no
  `#[test]` functions, so `cargo test` reported 0 tests. Each binary
  now has a `#[cfg(test)]` module that wraps the logic, yielding 6
  real test results.

PERFORMANCE

- Added `#[inline]` to all hot-path wrapper methods (`new`, `load`,
  `store`, `swap`, `compare_exchange`, `compare_exchange_weak`,
  `fetch_update`) and the public `encode_*` / `decode_*` helpers
  across all six atomic types. This helps downstream non-LTO builds
  avoid call overhead on these tiny wrappers.

OTHER

- **Benchmark "contended write" group renamed to
  `load_under_write_contention`** to accurately reflect what it
  measures (load latency on the main thread while background threads
  write, not write latency). A new `contended_store` group was added
  that benchmarks real `store` and `swap` latency under write
  contention. README tables updated with the corrected labels and
  fresh numbers.

# 0.2.0

BREAKING CHANGES

- MSRV bumped from 1.34.0 to 1.70.0.
- Rust edition updated from 2018 to 2021.
- Removed `once_cell` dependency in favor of `std::sync::OnceLock`.

BUG FIXES

- Fixed `encode_instant_to_duration` producing incorrect results for instants before the initialization baseline.
- Fixed serde test in `AtomicOptionInstant` that was incorrectly testing `AtomicOptionSystemTime`.
- Fixed doc comments in `AtomicInstant` and `AtomicOptionInstant` that incorrectly referenced `SystemTime`.

FEATURES

- Added `Debug` implementation for `AtomicSystemTime`, `AtomicOptionSystemTime`, `AtomicInstant`, and `AtomicOptionInstant`.
- Added `into_inner()` for `AtomicSystemTime`, `AtomicOptionSystemTime`, `AtomicInstant`, and `AtomicOptionInstant`.
- Added `Default` implementation for `AtomicDuration` (`Duration::ZERO`) and `AtomicOptionDuration` (`None`).
- Added `From` trait implementations for all six atomic types.

# 0.1.4 (Dec 26th, 2023)

FEATURES

- Exports `decode_duration`, `encode_duration`, `decode_option_duration`, `encode_option_duration`, `decode_instant_from_duration`, `encode_instant_to_duration`.
- Add `is_lock_free` fn for all atomic structs.

# 0.1.3 (Dec 24th, 2023)

FEATURES

- Replace `atomic` by using `core::sync::atomic::AtomicU128` in nightly or `portable-atomic` in stable.
- Add benchmarks

# 0.1.2 (Dec 23rd, 2023)

FEATURES

- `AtomicSystemTime` and `AtomicOptionSystemTime` implementations.
- `AtomicInstant` and `AtomicOptionInstant` implementations.

# 0.1.1 (Dec 22nd, 2023)

FEATURES

- `AtomicOptionDuration` implementation.
- Change `AtomicOption` implementation to keep the nanos information.

# 0.1.0 (Dec 22nd, 2023)

FEATURES

- `AtomicDuration` implementation.
