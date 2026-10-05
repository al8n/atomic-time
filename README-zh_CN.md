<div align="center">
<h1>Atomic Time</h1>
</div>
<div align="center">

线程安全的 Duration、SystemTime、Instant 及其 Option 变体的原子版本；在原生支持 `AtomicU128` 的平台上无锁，否则 `portable-atomic` 可能回退到全局锁

[<img alt="github" src="https://img.shields.io/badge/github-al8n/atomic--time-8da0cb?style=for-the-badge&logo=Github" height="22">][Github-url]
[<img alt="Build" src="https://img.shields.io/github/actions/workflow/status/al8n/atomic-time/ci.yml?logo=Github-Actions&style=for-the-badge" height="22">][CI-url]
[<img alt="codecov" src="https://img.shields.io/codecov/c/gh/al8n/atomic-time?style=for-the-badge&token=6R3QFWRWHL&logo=codecov" height="22">][codecov-url]

[<img alt="docs.rs" src="https://img.shields.io/badge/docs.rs-atomic--time-66c2a5?style=for-the-badge&labelColor=555555&logo=data:image/svg+xml;base64,PHN2ZyByb2xlPSJpbWciIHhtbG5zPSJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2ZyIgdmlld0JveD0iMCAwIDUxMiA1MTIiPjxwYXRoIGZpbGw9IiNmNWY1ZjUiIGQ9Ik00ODguNiAyNTAuMkwzOTIgMjE0VjEwNS41YzAtMTUtOS4zLTI4LjQtMjMuNC0zMy43bC0xMDAtMzcuNWMtOC4xLTMuMS0xNy4xLTMuMS0yNS4zIDBsLTEwMCAzNy41Yy0xNC4xIDUuMy0yMy40IDE4LjctMjMuNCAzMy43VjIxNGwtOTYuNiAzNi4yQzkuMyAyNTUuNSAwIDI2OC45IDAgMjgzLjlWMzk0YzAgMTMuNiA3LjcgMjYuMSAxOS45IDMyLjJsMTAwIDUwYzEwLjEgNS4xIDIyLjEgNS4xIDMyLjIgMGwxMDMuOS01MiAxMDMuOSA1MmMxMC4xIDUuMSAyMi4xIDUuMSAzMi4yIDBsMTAwLTUwYzEyLjItNi4xIDE5LjktMTguNiAxOS45LTMyLjJWMjgzLjljMC0xNS05LjMtMjguNC0yMy40LTMzLjd6TTM1OCAyMTQuOGwtODUgMzEuOXYtNjguMmw4NS0zN3Y3My4zek0xNTQgMTA0LjFsMTAyLTM4LjIgMTAyIDM4LjJ2LjZsLTEwMiA0MS40LTEwMi00MS40di0uNnptODQgMjkxLjFsLTg1IDQyLjV2LTc5LjFsODUtMzguOHY3NS40em0wLTExMmwtMTAyIDQxLjQtMTAyLTQxLjR2LS42bDEwMi0zOC4yIDEwMiAzOC4ydi42em0yNDAgMTEybC04NSA0Mi41di03OS4xbDg1LTM4Ljh2NzUuNHptMC0xMTJsLTEwMiA0MS40LTEwMi00MS40di0uNmwxMDItMzguMiAxMDIgMzguMnYuNnoiPjwvcGF0aD48L3N2Zz4K" height="20">][doc-url]
[<img alt="crates.io" src="https://img.shields.io/crates/v/atomic-time?style=for-the-badge&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBlbmNvZGluZz0iaXNvLTg4NTktMSI/Pg0KPCEtLSBHZW5lcmF0b3I6IEFkb2JlIElsbHVzdHJhdG9yIDE5LjAuMCwgU1ZHIEV4cG9ydCBQbHVnLUluIC4gU1ZHIFZlcnNpb246IDYuMDAgQnVpbGQgMCkgIC0tPg0KPHN2ZyB2ZXJzaW9uPSIxLjEiIGlkPSJMYXllcl8xIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHhtbG5zOnhsaW5rPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5L3hsaW5rIiB4PSIwcHgiIHk9IjBweCINCgkgdmlld0JveD0iMCAwIDUxMiA1MTIiIHhtbDpzcGFjZT0icHJlc2VydmUiPg0KPGc+DQoJPGc+DQoJCTxwYXRoIGQ9Ik0yNTYsMEwzMS41MjgsMTEyLjIzNnYyODcuNTI4TDI1Niw1MTJsMjI0LjQ3Mi0xMTIuMjM2VjExMi4yMzZMMjU2LDB6IE0yMzQuMjc3LDQ1Mi41NjRMNzQuOTc0LDM3Mi45MTNWMTYwLjgxDQoJCQlsMTU5LjMwMyw3OS42NTFWNDUyLjU2NHogTTEwMS44MjYsMTI1LjY2MkwyNTYsNDguNTc2bDE1NC4xNzQsNzcuMDg3TDI1NiwyMDIuNzQ5TDEwMS44MjYsMTI1LjY2MnogTTQzNy4wMjYsMzcyLjkxMw0KCQkJbC0xNTkuMzAzLDc5LjY1MVYyNDAuNDYxbDE1OS4zMDMtNzkuNjUxVjM3Mi45MTN6IiBmaWxsPSIjRkZGIi8+DQoJPC9nPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPGc+DQo8L2c+DQo8Zz4NCjwvZz4NCjxnPg0KPC9nPg0KPC9zdmc+DQo=" height="22">][crates-url]
[<img alt="crates.io" src="https://img.shields.io/crates/d/atomic-time?color=critical&logo=data:image/svg+xml;base64,PD94bWwgdmVyc2lvbj0iMS4wIiBzdGFuZGFsb25lPSJubyI/PjwhRE9DVFlQRSBzdmcgUFVCTElDICItLy9XM0MvL0RURCBTVkcgMS4xLy9FTiIgImh0dHA6Ly93d3cudzMub3JnL0dyYXBoaWNzL1NWRy8xLjEvRFREL3N2ZzExLmR0ZCI+PHN2ZyB0PSIxNjQ1MTE3MzMyOTU5IiBjbGFzcz0iaWNvbiIgdmlld0JveD0iMCAwIDEwMjQgMTAyNCIgdmVyc2lvbj0iMS4xIiB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHAtaWQ9IjM0MjEiIGRhdGEtc3BtLWFuY2hvci1pZD0iYTMxM3guNzc4MTA2OS4wLmkzIiB3aWR0aD0iNDgiIGhlaWdodD0iNDgiIHhtbG5zOnhsaW5rPSJodHRwOi8vd3d3LnczLm9yZy8xOTk5L3hsaW5rIj48ZGVmcz48c3R5bGUgdHlwZT0idGV4dC9jc3MiPjwvc3R5bGU+PC9kZWZzPjxwYXRoIGQ9Ik00NjkuMzEyIDU3MC4yNHYtMjU2aDg1LjM3NnYyNTZoMTI4TDUxMiA3NTYuMjg4IDM0MS4zMTIgNTcwLjI0aDEyOHpNMTAyNCA2NDAuMTI4QzEwMjQgNzgyLjkxMiA5MTkuODcyIDg5NiA3ODcuNjQ4IDg5NmgtNTEyQzEyMy45MDQgODk2IDAgNzYxLjYgMCA1OTcuNTA0IDAgNDUxLjk2OCA5NC42NTYgMzMxLjUyIDIyNi40MzIgMzAyLjk3NiAyODQuMTYgMTk1LjQ1NiAzOTEuODA4IDEyOCA1MTIgMTI4YzE1Mi4zMiAwIDI4Mi4xMTIgMTA4LjQxNiAzMjMuMzkyIDI2MS4xMkM5NDEuODg4IDQxMy40NCAxMDI0IDUxOS4wNCAxMDI0IDY0MC4xOTJ6IG0tMjU5LjItMjA1LjMxMmMtMjQuNDQ4LTEyOS4wMjQtMTI4Ljg5Ni0yMjIuNzItMjUyLjgtMjIyLjcyLTk3LjI4IDAtMTgzLjA0IDU3LjM0NC0yMjQuNjQgMTQ3LjQ1NmwtOS4yOCAyMC4yMjQtMjAuOTI4IDIuOTQ0Yy0xMDMuMzYgMTQuNC0xNzguMzY4IDEwNC4zMi0xNzguMzY4IDIxNC43MiAwIDExNy45NTIgODguODMyIDIxNC40IDE5Ni45MjggMjE0LjRoNTEyYzg4LjMyIDAgMTU3LjUwNC03NS4xMzYgMTU3LjUwNC0xNzEuNzEyIDAtODguMDY0LTY1LjkyLTE2NC45MjgtMTQ0Ljk2LTE3MS43NzZsLTI5LjUwNC0yLjU2LTUuODg4LTMwLjk3NnoiIGZpbGw9IiNmZmZmZmYiIHAtaWQ9IjM0MjIiIGRhdGEtc3BtLWFuY2hvci1pZD0iYTMxM3guNzc4MTA2OS4wLmkwIiBjbGFzcz0iIj48L3BhdGg+PC9zdmc+&style=for-the-badge" height="22">][crates-url]

<img alt="license" src="https://img.shields.io/badge/License-Apache%202.0/MIT-blue.svg?style=for-the-badge&fontColor=white&logoColor=f5c076&logo=data:image/svg+xml;base64,PCFET0NUWVBFIHN2ZyBQVUJMSUMgIi0vL1czQy8vRFREIFNWRyAxLjEvL0VOIiAiaHR0cDovL3d3dy53My5vcmcvR3JhcGhpY3MvU1ZHLzEuMS9EVEQvc3ZnMTEuZHRkIj4KDTwhLS0gVXBsb2FkZWQgdG86IFNWRyBSZXBvLCB3d3cuc3ZncmVwby5jb20sIFRyYW5zZm9ybWVkIGJ5OiBTVkcgUmVwbyBNaXhlciBUb29scyAtLT4KPHN2ZyBmaWxsPSIjZmZmZmZmIiBoZWlnaHQ9IjgwMHB4IiB3aWR0aD0iODAwcHgiIHZlcnNpb249IjEuMSIgaWQ9IkNhcGFfMSIgeG1sbnM9Imh0dHA6Ly93d3cudzMub3JnLzIwMDAvc3ZnIiB4bWxuczp4bGluaz0iaHR0cDovL3d3dy53My5vcmcvMTk5OS94bGluayIgdmlld0JveD0iMCAwIDI3Ni43MTUgMjc2LjcxNSIgeG1sOnNwYWNlPSJwcmVzZXJ2ZSIgc3Ryb2tlPSIjZmZmZmZmIj4KDTxnIGlkPSJTVkdSZXBvX2JnQ2FycmllciIgc3Ryb2tlLXdpZHRoPSIwIi8+Cg08ZyBpZD0iU1ZHUmVwb190cmFjZXJDYXJyaWVyIiBzdHJva2UtbGluZWNhcD0icm91bmQiIHN0cm9rZS1saW5lam9pbj0icm91bmQiLz4KDTxnIGlkPSJTVkdSZXBvX2ljb25DYXJyaWVyIj4gPGc+IDxwYXRoIGQ9Ik0xMzguMzU3LDBDNjIuMDY2LDAsMCw2Mi4wNjYsMCwxMzguMzU3czYyLjA2NiwxMzguMzU3LDEzOC4zNTcsMTM4LjM1N3MxMzguMzU3LTYyLjA2NiwxMzguMzU3LTEzOC4zNTcgUzIxNC42NDgsMCwxMzguMzU3LDB6IE0xMzguMzU3LDI1OC43MTVDNzEuOTkyLDI1OC43MTUsMTgsMjA0LjcyMywxOCwxMzguMzU3UzcxLjk5MiwxOCwxMzguMzU3LDE4IHMxMjAuMzU3LDUzLjk5MiwxMjAuMzU3LDEyMC4zNTdTMjA0LjcyMywyNTguNzE1LDEzOC4zNTcsMjU4LjcxNXoiLz4gPHBhdGggZD0iTTE5NC43OTgsMTYwLjkwM2MtNC4xODgtMi42NzctOS43NTMtMS40NTQtMTIuNDMyLDIuNzMyYy04LjY5NCwxMy41OTMtMjMuNTAzLDIxLjcwOC0zOS42MTQsMjEuNzA4IGMtMjUuOTA4LDAtNDYuOTg1LTIxLjA3OC00Ni45ODUtNDYuOTg2czIxLjA3Ny00Ni45ODYsNDYuOTg1LTQ2Ljk4NmMxNS42MzMsMCwzMC4yLDcuNzQ3LDM4Ljk2OCwyMC43MjMgYzIuNzgyLDQuMTE3LDguMzc1LDUuMjAxLDEyLjQ5NiwyLjQxOGM0LjExOC0yLjc4Miw1LjIwMS04LjM3NywyLjQxOC0xMi40OTZjLTEyLjExOC0xNy45MzctMzIuMjYyLTI4LjY0NS01My44ODItMjguNjQ1IGMtMzUuODMzLDAtNjQuOTg1LDI5LjE1Mi02NC45ODUsNjQuOTg2czI5LjE1Miw2NC45ODYsNjQuOTg1LDY0Ljk4NmMyMi4yODEsMCw0Mi43NTktMTEuMjE4LDU0Ljc3OC0zMC4wMDkgQzIwMC4yMDgsMTY5LjE0NywxOTguOTg1LDE2My41ODIsMTk0Ljc5OCwxNjAuOTAzeiIvPiA8L2c+IDwvZz4KDTwvc3ZnPg==" height="22">

[English](./README.md) | 简体中文

</div>

## 简介

`atomic-time` 提供了 Rust 标准时间类型的线程安全原子版本。在原生支持 `AtomicU128` 的平台上，这些操作是无锁的；否则 [`portable-atomic`](https://crates.io/crates/portable-atomic) 可能回退到全局锁。所有类型底层使用 `AtomicU128`（通过 `portable-atomic`），并暴露与标准 `std::sync::atomic` 类型相同的 API 模式（`load`、`store`、`swap`、`compare_exchange`、`compare_exchange_weak`、`fetch_update`）。

### 类型

| 类型 | 包装 | `no_std` | `arbitrary` | `quickcheck` / `proptest` |
|------|------|----------|-------------|--------------------------|
| `AtomicDuration` | `Duration` | 支持 | 启用 `std` 时支持 | 启用 `std` 时支持 |
| `AtomicOptionDuration` | `Option<Duration>` | 支持 | 启用 `std` 时支持 | 启用 `std` 时支持 |
| `AtomicSystemTime` | `SystemTime` | 不支持 | 启用 `std` 时支持 | 启用 `std` 时支持 |
| `AtomicOptionSystemTime` | `Option<SystemTime>` | 不支持 | 启用 `std` 时支持 | 启用 `std` 时支持 |
| `AtomicInstant` | `Instant` | 不支持 | 不支持 | 不支持 |
| `AtomicOptionInstant` | `Option<Instant>` | 不支持 | 不支持 | 不支持 |

## 安装

```toml
[dependencies]
atomic-time = "1"
```

### Feature Flags

| Feature | 默认开启 | 说明 |
|---------|---------|------|
| `std` | 是 | 启用 `SystemTime` 和 `Instant` 类型 |
| `serde` | 否 | 为所有类型启用 `Serialize`/`Deserialize`，也可用于 `no_std` 构建 |
| `arbitrary` | 否 | 为 Duration 和 SystemTime 类型启用 [`arbitrary`](https://crates.io/crates/arbitrary)；需要 `std` |
| `quickcheck` | 否 | 为 Duration 和 SystemTime 类型启用 [`quickcheck`](https://crates.io/crates/quickcheck)，并提供快照 `Clone` 实现 |
| `proptest` | 否 | 为 Duration 和 SystemTime 类型启用 [`proptest`](https://crates.io/crates/proptest) 策略 |

在 `no_std` 环境下使用（仅 `AtomicDuration` 和 `AtomicOptionDuration` 可用）：

```toml
[dependencies]
atomic-time = { version = "1", default-features = false }
```

在 `no_std` 构建中也可以通过 `features = ["serde"]` 启用可选的 `serde` 特性。

三种生成/属性测试集成都需要 `std`。其中 `arbitrary` 也需要 `std`，因为当前上游
`arbitrary` v1 crate 本身依赖 `std`。可选择启用其中一种集成：

```toml
[dependencies]
atomic-time = { version = "1", features = ["arbitrary"] }
# 或：atomic-time = { version = "1", features = ["quickcheck"] }
# 或：atomic-time = { version = "1", features = ["proptest"] }
```

`quickcheck` 特性会为 `AtomicDuration`、`AtomicOptionDuration`、
`AtomicSystemTime` 和 `AtomicOptionSystemTime` 实现 `Clone`。克隆操作会执行
一次 `SeqCst` 加载；如果同时存在其他线程写入，克隆值就是该加载原子线性化时刻观察到的值。

`AtomicInstant` 和 `AtomicOptionInstant` 有意不实现 `arbitrary`、
`quickcheck` 或 `proptest` trait（这些特性也不会为它们添加 `Clone`）。它们的编码依赖
进程本地基线，因此 seed 或 corpus 无法在不同进程运行之间产生可移植且确定的值。

某些没有原生 CAS 支持的裸机目标，最终应用必须通过 Cargo feature unification 启用 `portable-atomic` 的 `critical-section` feature，并提供适用于目标的 `critical-section` 实现；或者采用官方 [`portable-atomic` 指南](https://github.com/taiki-e/portable-atomic#optional-features) 中的其他安全配置。

### 原子操作

六种原子类型都提供 `is_always_lock_free`、`try_update`、`update`、
`fetch_min` 和 `fetch_max`；现有的 `fetch_update` 仍保留以兼容已有代码。
`fetch_min` 和 `fetch_max` 返回操作前观察到的旧值。对于 `Option` 类型，排序为
`None < Some`；`Instant` 的比较只适用于使用同一进程本地基线的值。

`AtomicDuration` 和 `AtomicOptionDuration` 还提供
`fetch_saturating_add` 与 `fetch_saturating_sub`，并返回旧值。对于
`AtomicDuration`，它们分别饱和到 `Duration::MAX` 和 `Duration::ZERO`；对于
`AtomicOptionDuration`，`Some` 值执行饱和，`None` 保持为 `None`（不会将其视为零）。
这些方法有意命名为 `fetch_saturating_add/sub`，而不是 `fetch_add/sub`，以避免暗示整数
wrapping；饱和加减辅助方法仅适用于 Duration 类型。

### 时间语义

`AtomicSystemTime` 和 `AtomicOptionSystemTime` 只接受不早于 `SystemTime::UNIX_EPOCH` 的值；早于该时间的值会触发 panic。

`AtomicInstant` 和 `AtomicOptionInstant` 使用由 `SystemTime::now()` 与 `Instant::now()` 初始化的进程本地基线来编码 `Instant`。在同一进程内，平台 `Instant` 可表示范围内的值可以精确往返。跨进程或重启时，该编码不可移植，解码只能近似表示墙上时钟时间；系统时钟调整可能改变这种跨进程或重启后的含义。休眠期间的行为遵循平台对 `Instant` 的语义。不要将编码后的 instant 持久化为 deadline。如果极端 `Duration` 超出平台 `Instant` 的可表示范围，解码会回退到进程基线，而不是 panic。

## 示例

```rust
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::time::Duration;
use atomic_time::AtomicDuration;

let timeout = Arc::new(AtomicDuration::new(Duration::from_secs(30)));

// 从另一个线程更新
let timeout_clone = timeout.clone();
std::thread::spawn(move || {
    timeout_clone.store(Duration::from_secs(60), Ordering::Release);
});
```

```rust
use std::sync::atomic::Ordering;
use std::time::Instant;
use atomic_time::AtomicOptionInstant;

// 追踪事件最后发生的时间
let last_event = AtomicOptionInstant::none();
assert_eq!(last_event.load(Ordering::Relaxed), None);

last_event.store(Some(Instant::now()), Ordering::Release);
assert!(last_event.load(Ordering::Acquire).is_some());
```

## 基准测试

在 `benchmark/` 目录下运行 `cargo bench`。Apple M4 Pro。

### Duration (`cargo bench --bench duration`)

| 实现 | 单线程读取 | 单线程写入 | 读竞争 | 写竞争下读取 | 写竞争下存储 |
|---|---|---|---|---|---|
| `AtomicDuration` | 1.04 ns | 0.72 ns | 1.08 ns | 4.44 ns | 10.7 ns |
| `AtomicOptionDuration` | 1.16 ns | 0.74 ns | 1.20 ns | 4.73 ns | 14.5 ns |
| `ArcSwap<Duration>` | 2.30 ns | 86.5 ns | 2.38 ns | 15.5 ns | 1,400 ns |
| `parking_lot::RwLock` | 3.40 ns | 2.09 ns | 9.3 ns | 241.8 ns | 37.7 ns |
| `std::sync::RwLock` | 4.44 ns | 2.26 ns | 411.2 ns | 89.0 ns | 36.8 ns |

### Instant (`cargo bench --bench instant`)

| 实现 | 单线程读取 | 单线程写入 | 读竞争 | 写竞争下读取 | 写竞争下存储 |
|---|---|---|---|---|---|
| `AtomicInstant` | 2.16 ns | 3.52 ns | 2.17 ns | 14.97 ns | 22.7 ns |
| `AtomicOptionInstant` | 2.36 ns | 3.51 ns | 2.40 ns | 17.63 ns | 21.2 ns |
| `ArcSwap<Instant>` | 2.95 ns | 74.9 ns | 2.92 ns | 17.53 ns | 972 ns |
| `parking_lot::RwLock` | 3.43 ns | 2.10 ns | 81.3 ns | 213.9 ns | 26.9 ns |
| `std::sync::RwLock` | 4.48 ns | 2.28 ns | 422.3 ns | 87.7 ns | 76.9 ns |

### SystemTime (`cargo bench --bench system_time`)

| 实现 | 单线程读取 | 单线程写入 | 读竞争 | 写竞争下读取 | 写竞争下存储 |
|---|---|---|---|---|---|
| `AtomicSystemTime` | 1.26 ns | 3.41 ns | 1.28 ns | 8.89 ns | 27.1 ns |
| `AtomicOptionSystemTime` | 1.25 ns | 3.47 ns | 1.30 ns | 9.17 ns | 25.2 ns |
| `ArcSwap<SystemTime>` | 2.29 ns | 83.7 ns | 2.39 ns | 16.4 ns | 1,227 ns |
| `parking_lot::RwLock` | 3.50 ns | 2.13 ns | 22.0 ns | 204.5 ns | 31.0 ns |
| `std::sync::RwLock` | 4.69 ns | 2.31 ns | 554.2 ns | 84.4 ns | 38.7 ns |

> **读竞争** = 4 个后台线程同时读取；**写竞争下读取** = 4 个后台线程写入，主线程测量读取延迟；**写竞争下存储** = 4 个后台线程写入，主线程测量存储延迟。所有数据来自 Apple M4 Pro。

## MSRV

最低支持的 Rust 版本为 **1.85**。

## 许可证

`atomic-time` 使用 MIT 许可证和 Apache 许可证（2.0 版本）双重授权。

详情请参阅 [LICENSE-APACHE](LICENSE-APACHE)、[LICENSE-MIT](LICENSE-MIT)。

Copyright (c) 2026 Al Liu.

[Github-url]: https://github.com/al8n/atomic-time/
[CI-url]: https://github.com/al8n/atomic-time/actions/workflows/ci.yml
[doc-url]: https://docs.rs/atomic-time
[crates-url]: https://crates.io/crates/atomic-time
[codecov-url]: https://app.codecov.io/gh/al8n/atomic-time/
