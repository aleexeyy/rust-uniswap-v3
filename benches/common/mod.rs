#![allow(dead_code)]

use alloy_primitives::{I256, U256};
use clmm_swap_math::math::{
    bit_math, math_helpers, sqrt_price_math, swap_math, tick_bitmap, tick_math,
};
use clmm_swap_math::{FastMap, RESOLUTION};
use criterion::{BenchmarkId, Criterion, Throughput, black_box};

pub fn bench_tick_math(c: &mut Criterion) {
    let mut group = c.benchmark_group("tick_math");

    group.throughput(Throughput::Elements(1));

    group.bench_function(BenchmarkId::new("get_sqrt_ratio_at_tick", "0"), |b| {
        b.iter(|| tick_math::get_sqrt_ratio_at_tick(black_box(0)).unwrap());
    });

    group.bench_function(BenchmarkId::new("get_sqrt_ratio_at_tick", "max"), |b| {
        b.iter(|| tick_math::get_sqrt_ratio_at_tick(black_box(tick_math::MAX_TICK - 1)).unwrap());
    });

    let mid_ratio = tick_math::get_sqrt_ratio_at_tick(0).unwrap();
    group.bench_function("get_tick_at_sqrt_ratio", |b| {
        b.iter(|| tick_math::get_tick_at_sqrt_ratio(black_box(mid_ratio)).unwrap());
    });
}

pub fn bench_sqrt_price_math(c: &mut Criterion) {
    let mut group = c.benchmark_group("sqrt_price_math");

    let sqrt_price = U256::from(1u128) << RESOLUTION;
    let liquidity = 1_000_000_000_000_000_000u128; // 1e18
    let amount = U256::from(1_000_000_000_000_000_000u128);

    group.bench_function("next_sqrt_price_from_input_zero_for_one", |b| {
        b.iter(|| {
            sqrt_price_math::get_next_sqrt_price_from_input(
                black_box(sqrt_price),
                black_box(liquidity),
                black_box(amount),
                true,
            )
            .unwrap()
        })
    });

    group.bench_function("next_sqrt_price_from_input_one_for_zero", |b| {
        b.iter(|| {
            sqrt_price_math::get_next_sqrt_price_from_input(
                black_box(sqrt_price),
                black_box(liquidity),
                black_box(amount),
                false,
            )
            .unwrap()
        })
    });

    group.bench_function("amount_0_delta_base", |b| {
        b.iter(|| {
            sqrt_price_math::get_amount_0_delta_base(
                black_box(sqrt_price),
                black_box(sqrt_price + U256::from(10_000u64)),
                black_box(liquidity),
                true,
            )
            .unwrap()
        })
    });

    group.bench_function("amount_1_delta_base", |b| {
        b.iter(|| {
            sqrt_price_math::get_amount_1_delta_base(
                black_box(sqrt_price),
                black_box(sqrt_price + U256::from(10_000u64)),
                black_box(liquidity),
                true,
            )
            .unwrap()
        })
    });
}

pub fn bench_swap_math(c: &mut Criterion) {
    let mut group = c.benchmark_group("swap_math");

    let sqrt_price = U256::from(1u128) << RESOLUTION;
    let sqrt_target = sqrt_price + U256::from(1_000_000u64);
    let liquidity = 1_000_000_000_000_000_000u128;
    let amount_remaining = I256::from_raw(U256::from(1_000_000_000_000_000_000u128));
    let fee_pips = 3000u32;

    group.bench_function("compute_swap_step_exact_in", |b| {
        b.iter(|| {
            swap_math::compute_swap_step(
                black_box(sqrt_price),
                black_box(sqrt_target),
                black_box(liquidity),
                black_box(amount_remaining),
                black_box(fee_pips),
            )
            .unwrap()
        })
    });

    let amount_out = -amount_remaining;
    group.bench_function("compute_swap_step_exact_out", |b| {
        b.iter(|| {
            swap_math::compute_swap_step(
                black_box(sqrt_price),
                black_box(sqrt_target),
                black_box(liquidity),
                black_box(amount_out),
                black_box(fee_pips),
            )
            .unwrap()
        })
    });
}

pub fn bench_math_helpers(c: &mut Criterion) {
    let mut group = c.benchmark_group("math_helpers");

    // Use non-overflowing inputs that exercise the fast path,
    // mirroring values from the unit tests.
    let a = U256::from(1000u16);
    let b = U256::from(2000u16);
    let denom = U256::from(100u8);

    group.bench_function("mul_div", |bch| {
        bch.iter(|| math_helpers::mul_div(black_box(a), black_box(b), black_box(denom)).unwrap())
    });

    group.bench_function("mul_div_rounding_up", |bch| {
        bch.iter(|| {
            math_helpers::mul_div_rounding_up(black_box(a), black_box(b), black_box(denom)).unwrap()
        })
    });
}

pub fn bench_tick_bitmap(c: &mut Criterion) {
    let mut group = c.benchmark_group("tick_bitmap");

    let ticks = vec![-200, -55, -4, 70, 78, 84, 139, 240, 535];
    let mut bitmap: FastMap<i16, U256> = FastMap::default();
    for &t in &ticks {
        tick_bitmap::flip_tick(&mut bitmap, t, 1).unwrap();
    }

    group.bench_function("next_initialized_tick_within_one_word_lte_false", |b| {
        b.iter(|| {
            tick_bitmap::next_initialized_tick_within_one_word(
                black_box(&bitmap),
                black_box(78),
                1,
                false,
            )
            .unwrap()
        })
    });

    group.bench_function("next_initialized_tick_within_one_word_lte_true", |b| {
        b.iter(|| {
            tick_bitmap::next_initialized_tick_within_one_word(
                black_box(&bitmap),
                black_box(78),
                1,
                true,
            )
            .unwrap()
        })
    });
}

pub fn bench_bit_math(c: &mut Criterion) {
    let mut group = c.benchmark_group("bit_math");

    let x = U256::from(u128::MAX);

    group.bench_function("most_significant_bit", |b| {
        b.iter(|| bit_math::most_significant_bit(black_box(x)).unwrap())
    });

    group.bench_function("least_significant_bit", |b| {
        b.iter(|| bit_math::least_significant_bit(black_box(x)).unwrap())
    });
}

// NOTE: Benchmarks execute ~1e5 iterations per sample.
// In local profiling with `cargo bench`, hot spots were:
// - `sqrt_price_math::get_next_sqrt_price_from_input`
// - `swap_math::compute_swap_step`
// - `math_helpers::mul_div`
// These benches exist to catch regressions in those paths.
