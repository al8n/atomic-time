# UNRELEASED

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
