use crate::U256_10000;
use crate::error::{Error, SwapError};
use crate::swap_math::compute_swap_step;
use crate::tick_bitmap::next_initialized_tick_within_one_word;
use crate::tick_math::{
    MAX_SQRT_RATIO, MAX_TICK, MIN_SQRT_RATIO, MIN_TICK, get_sqrt_ratio_at_tick,
    get_tick_at_sqrt_ratio,
};
use crate::v3_pool::V3Pool;
use alloy::providers::Provider;
use alloy_primitives::{I256, U256};
use std::ops::{Add, Sub};

pub fn calculate_sqrt_price_limit(
    sqrt_price_x96: U256,
    zero_for_one: bool,
    tolerance: f32,
) -> U256 {
    let slippage_bps = tolerance * 10_000.0;

    if zero_for_one {
        (sqrt_price_x96 * U256::from(10000.0 - slippage_bps)) / U256_10000
    } else {
        (sqrt_price_x96 * U256::from(10000.0 + slippage_bps)) / U256_10000
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Slot0 {
    pub(crate) sqrt_price_x96: U256,
    pub(crate) tick: i32,
}

impl Default for Slot0 {
    fn default() -> Self {
        Self {
            sqrt_price_x96: U256::ZERO,
            tick: 0i32,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct SwapParams {
    zero_for_one: bool,
    amount_specified: I256,
    sqrt_price_limit_x96: U256,
}

#[derive(Copy, Clone, Debug)]
pub struct SwapResult {
    pub amount0_delta: I256,
    pub amount1_delta: I256,
    pub fees_paid: U256,
}

// the top level state of the swap, the results of which are recorded in storage at the end
pub struct SwapState {
    // the amount remaining to be swapped in/out of the input/output asset
    amount_specified_remaining: I256,
    // the amount already swapped out/in of the output/input asset
    amount_calculated: I256,
    // current sqrt(price)
    sqrt_price_x96: U256,
    // the tick associated with the current price
    tick: i32,
    // the current liquidity in range
    liquidity: u128,
    // accumulated swap fees
    swap_fee: U256,
}

pub struct StepComputations {
    // the price at the beginning of the step
    sqrt_price_start_x96: U256,
    // the next tick to swap to from the current tick in the swap direction
    tick_next: i32,
    // whether tickNext is initialized or not
    initialized: bool,
    // sqrt(price) for the next tick (1/0)
    sqrt_price_next_x96: U256,
    // how much is being swapped in this step
    amount_in: U256,
    // how much is being swapped out
    amount_out: U256,
    // how much fee is being paid in
    fee_amount: U256,
}

impl Default for StepComputations {
    fn default() -> Self {
        Self {
            sqrt_price_start_x96: U256::ZERO,
            tick_next: 0,
            initialized: false,
            sqrt_price_next_x96: U256::ZERO,
            amount_in: U256::ZERO,
            amount_out: U256::ZERO,
            fee_amount: U256::ZERO,
        }
    }
}
impl<P: Provider + Send + Sync + 'static> V3Pool<P> {
    pub fn swap(&self, params: SwapParams) -> Result<SwapResult, Error> {
        let amount_specified = params.amount_specified;
        if amount_specified.is_zero() {
            return Err(Error::SwapError(SwapError::AmountSpecifiedIsZero));
        }
        if self.liquidity == 0 {
            return Err(Error::SwapError(SwapError::LiquidityIsZero));
        }

        let zero_for_one = params.zero_for_one;
        let sqrt_price_limit_x96 = params.sqrt_price_limit_x96;
        if zero_for_one {
            if (sqrt_price_limit_x96 >= self.slot0.sqrt_price_x96)
                || (sqrt_price_limit_x96 <= MIN_SQRT_RATIO)
            {
                return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds));
            }
        } else if (sqrt_price_limit_x96 <= self.slot0.sqrt_price_x96)
            || (sqrt_price_limit_x96 >= MAX_SQRT_RATIO)
        {
            return Err(Error::SwapError(SwapError::SqrtPriceOutOfBounds));
        }

        let exact_input: bool = amount_specified.is_positive();

        let mut state: SwapState = SwapState {
            amount_specified_remaining: amount_specified,
            amount_calculated: I256::ZERO,
            sqrt_price_x96: self.slot0.sqrt_price_x96,
            tick: self.slot0.tick,
            liquidity: self.liquidity,
            swap_fee: U256::ZERO,
        };

        while (state.amount_specified_remaining != I256::ZERO)
            && (state.sqrt_price_x96 != sqrt_price_limit_x96)
        {
            let mut step: StepComputations = StepComputations::default();

            step.sqrt_price_start_x96 = state.sqrt_price_x96;

            (step.tick_next, step.initialized) = next_initialized_tick_within_one_word(
                &self.bitmap,
                state.tick,
                self.tick_spacing,
                zero_for_one,
            )?;

            if step.tick_next < MIN_TICK {
                step.tick_next = MIN_TICK;
            } else if step.tick_next > MAX_TICK {
                step.tick_next = MAX_TICK;
            }

            step.sqrt_price_next_x96 = get_sqrt_ratio_at_tick(step.tick_next)?;

            (
                state.sqrt_price_x96,
                step.amount_in,
                step.amount_out,
                step.fee_amount,
            ) = compute_swap_step(
                state.sqrt_price_x96,
                if zero_for_one {
                    if step.sqrt_price_next_x96 < sqrt_price_limit_x96 {
                        sqrt_price_limit_x96
                    } else {
                        step.sqrt_price_next_x96
                    }
                } else if step.sqrt_price_next_x96 > sqrt_price_limit_x96 {
                    sqrt_price_limit_x96
                } else {
                    step.sqrt_price_next_x96
                },
                state.liquidity,
                state.amount_specified_remaining,
                self.fee_pips,
            )?;

            state.swap_fee += step.fee_amount;

            if exact_input {
                state.amount_specified_remaining -=
                    I256::from_raw(step.amount_in + step.fee_amount);
                state.amount_calculated =
                    state.amount_calculated.sub(I256::from_raw(step.amount_out));
            } else {
                state.amount_specified_remaining += I256::from_raw(step.amount_out);
                state.amount_calculated = state
                    .amount_calculated
                    .add(I256::from_raw(step.amount_in + step.fee_amount));
            }

            if state.sqrt_price_x96 == step.sqrt_price_next_x96 {
                if step.initialized {
                    if let Some(liquidity_net) = self.get_liquidity_net(&step.tick_next) {
                        if zero_for_one {
                            if liquidity_net >= 0 {
                                state.liquidity = state
                                    .liquidity
                                    .checked_sub(liquidity_net as u128)
                                    .ok_or(SwapError::LiquidityIsZero)?;
                            } else {
                                state.liquidity = state
                                    .liquidity
                                    .checked_add((-liquidity_net) as u128)
                                    .ok_or(SwapError::LiquidityIsZero)?;
                            }
                        } else if liquidity_net >= 0 {
                            state.liquidity = state
                                .liquidity
                                .checked_add(liquidity_net as u128)
                                .ok_or(SwapError::LiquidityIsZero)?;
                        } else {
                            state.liquidity = state
                                .liquidity
                                .checked_sub((-liquidity_net) as u128)
                                .ok_or(SwapError::LiquidityIsZero)?;
                        }
                    } else {
                        return Err(Error::SwapError(SwapError::LiquidityIsZero));
                    }

                    // TODO: Need to think, if I need to write something there
                }
                state.tick = if zero_for_one {
                    step.tick_next - 1
                } else {
                    step.tick_next
                };
            } else if state.sqrt_price_x96 != step.sqrt_price_start_x96 {
                state.tick = get_tick_at_sqrt_ratio(state.sqrt_price_x96)?;
            }
        }

        let (amount0, amount1): (I256, I256) = if zero_for_one == exact_input {
            (
                amount_specified - state.amount_specified_remaining,
                state.amount_calculated,
            )
        } else {
            (
                state.amount_calculated,
                amount_specified - state.amount_specified_remaining,
            )
        };

        Ok(SwapResult {
            amount0_delta: amount0,
            amount1_delta: amount1,
            fees_paid: state.swap_fee,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::address;
    use rustc_hash::FxHashMap;
    use std::str::FromStr;
    use std::sync::Arc;

    use crate::v3_pool::TickInfo;
    use alloy::network::Ethereum;
    use alloy::providers::RootProvider;
    // ---------------- Dummy Provider for tests ----------------

    #[derive(Clone)]
    struct DummyProvider;

    impl Provider for DummyProvider {
        fn root(&self) -> &RootProvider<Ethereum> {
            // swap() never touches the provider in these tests.
            // If this is ever called, it's a bug in the test wiring.
            unimplemented!("DummyProvider::root should not be used in swap unit tests");
        }
    }

    type TestPool = V3Pool<DummyProvider>;

    fn make_basic_pool(
        sqrt_price_x96: U256,
        tick: i32,
        liquidity: u128,
        fee_pips: u32,
        bitmap: FxHashMap<i16, U256>,
    ) -> TestPool {
        let provider = Arc::new(DummyProvider);

        let pool_address = address!("0x1000000000000000000000000000000000000000");
        let token0 = address!("0x0000000000000000000000000000000000000001");
        let token1 = address!("0x0000000000000000000000000000000000000002");

        let mut pool = TestPool::new(pool_address, token0, token1, fee_pips, provider);

        pool.slot0 = Slot0 {
            sqrt_price_x96,
            tick,
        };
        pool.liquidity = liquidity;
        pool.tick_spacing = 1; // simplest spacing
        pool.bitmap = bitmap;

        pool
    }

    fn default_bitmap() -> FxHashMap<i16, U256> {
        FxHashMap::default()
    }

    // ---------------- Basic validation tests ----------------

    #[test]
    fn swap_rejects_zero_amount_specified() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        let params = SwapParams {
            zero_for_one: true,
            amount_specified: I256::ZERO,
            sqrt_price_limit_x96: sqrt_price - U256::from(1u8),
        };

        let err = pool.swap(params).unwrap_err();

        match err {
            Error::SwapError(SwapError::AmountSpecifiedIsZero) => {}
            other => panic!("expected AmountSpecifiedIsZero, got: {:?}", other),
        }
    }

    #[test]
    fn swap_rejects_sqrt_price_limit_out_of_bounds_zero_for_one() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        // limit >= current price should be rejected for zero_for_one
        let params_eq = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: sqrt_price, // equal
        };
        let err_eq = pool.swap(params_eq).unwrap_err();
        match err_eq {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (eq case), got: {:?}", other),
        }

        // limit <= MIN_SQRT_RATIO should also be rejected
        let params_min = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: MIN_SQRT_RATIO, // too low or equal
        };
        let err_min = pool.swap(params_min).unwrap_err();
        match err_min {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (min case), got: {:?}", other),
        }
    }

    #[test]
    fn swap_rejects_sqrt_price_limit_out_of_bounds_one_for_zero() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, default_bitmap());

        // limit <= current price should be rejected for one_for_zero
        let params_eq = SwapParams {
            zero_for_one: false,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: sqrt_price, // equal
        };
        let err_eq = pool.swap(params_eq).unwrap_err();
        match err_eq {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (eq case), got: {:?}", other),
        }

        // limit >= MAX_SQRT_RATIO should be rejected
        let params_max = SwapParams {
            zero_for_one: false,
            amount_specified: I256::from_raw(U256::from(1_000u64)),
            sqrt_price_limit_x96: MAX_SQRT_RATIO, // too high or equal
        };
        let err_max = pool.swap(params_max).unwrap_err();
        match err_max {
            Error::SwapError(SwapError::SqrtPriceOutOfBounds) => {}
            other => panic!("expected SqrtPriceOutOfBounds (max case), got: {:?}", other),
        }
    }

    // ---------------- Behavioural / invariants tests ----------------

    #[test]
    fn swap_with_zero_liquidity_does_not_change_amounts_or_charge_fees() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let pool = make_basic_pool(sqrt_price, 0, 0u128, 3000, default_bitmap());

        let limit = sqrt_price - U256::from(1u8);

        let params = SwapParams {
            zero_for_one: true,
            amount_specified: I256::from_raw(U256::from(1_000_000u64)),
            sqrt_price_limit_x96: limit,
        };

        let result = pool.swap(params);

        // With zero liquidity, we can't actually trade anything.
        assert!(matches!(
            result,
            Err(Error::SwapError(SwapError::LiquidityIsZero))
        ));
    }

    #[test]
    fn swap_exact_input_one_for_zero_has_expected_signs() {
        let sqrt_price = get_sqrt_ratio_at_tick(0).unwrap();
        let mut bitmap = FxHashMap::default();
        bitmap.insert(0_i16, U256::from(1u8));

        let pool = make_basic_pool(sqrt_price, 0, 1_000_000u128, 3000, bitmap);

        let limit = sqrt_price * U256::from(2u8); // higher price, but < MAX_SQRT_RATIO
        assert!(limit < MAX_SQRT_RATIO);

        let amount = U256::from_str("1000000000000000000").unwrap(); // 1e18

        let params = SwapParams {
            zero_for_one: false, // one-for-zero
            amount_specified: I256::from_raw(amount),
            sqrt_price_limit_x96: limit,
        };

        let result = pool.swap(params).unwrap();

        // one-for-zero, exact input: pool receives token1, sends token0.
        // So amount1_delta >= 0, amount0_delta <= 0.
        assert!(result.amount1_delta >= I256::ZERO);
        assert!(result.amount0_delta <= I256::ZERO);

        assert!(
            result.amount0_delta != I256::ZERO || result.amount1_delta != I256::ZERO,
            "expected some swap to occur"
        );
        assert!(result.fees_paid >= U256::ZERO);
    }

    fn build_pool_for_js_case() -> TestPool {
        let provider = Arc::new(DummyProvider);

        // Addresses from the JS run
        let pool_address = address!("0xBfd25092d6d5396CfA88d867c0cC73B7603b4aD8");
        let token0 = address!("0x420698CFdEDdEa6bc78D59bC17798113ad278F9D");
        let token1 = address!("0xC02aaA39b223FE8D0A0e5C4F27eAd9083C756Cc2");

        let mut pool = TestPool::new(pool_address, token0, token1, 3000, provider);

        pool.slot0 = Slot0 {
            sqrt_price_x96: U256::from_str("1046706758115479018135889").unwrap(),
            tick: -224701,
        };
        pool.liquidity = 203624297715738503472u128;

        pool.tick_spacing = 60;

        let mut bitmap: FxHashMap<i16, U256> = FxHashMap::default();
        bitmap.insert(
            -15_i16,
            U256::from_str("39614081257132168796771975168").unwrap(),
        );
        bitmap.insert(
            57_i16,
            U256::from_str("50216813883093446110686315385661331328818843555712276103168").unwrap(),
        );

        let mut ticks: FxHashMap<i32, TickInfo> = FxHashMap::default();

        ticks.insert(
            -224700,
            TickInfo {
                word_position: -15,
                liquidity_gross: 203624287356963452704,
                liquidity_net: -203624287356963452704,
            },
        );

        ticks.insert(
            887220,
            TickInfo {
                word_position: 57,
                liquidity_gross: 10358775050768,
                liquidity_net: -10358775050768,
            },
        );
        pool.bitmap = bitmap;
        pool.ticks = ticks;

        pool
    }

    #[test]
    fn swap_matches_js_single_case() {
        // Arrange: pool in the same state as the JS simulation
        let pool = build_pool_for_js_case();

        // JS run parameters (off-chain simulation)
        let zero_for_one = false; // Direction: false
        let amount_specified = I256::from_raw(U256::from(1_098_120u64));

        // JS computed sqrtPriceLimitX96 using a 0.5% slippage, zeroForOne = false.
        // We recompute it here in Rust to mirror that logic:
        let slippage_bps = 0.5; // 0.5% = 50 bps
        let sqrt_price_start = pool.slot0.sqrt_price_x96;
        let sqrt_price_limit_x96 =
            calculate_sqrt_price_limit(sqrt_price_start, zero_for_one, slippage_bps);

        let params = SwapParams {
            zero_for_one,
            amount_specified,
            sqrt_price_limit_x96,
        };

        // Act
        let result = pool.swap(params).expect("swap should succeed");

        // JS output snapshot:
        // {
        // amountOut: 6222896066140743n,
        // amountUsed: 1098120n,
        // newSqrtPriceX96: 1055080413701515132449498n
        // }
        // For zeroForOne == false and exact input, the pool receives token1
        // and sends token0, so the token1 delta should be >= 0 and
        // correspond to the JS amountOut.

        let expected_amount_out = I256::from_raw(-U256::from(6222896066140743u64));
        let expected_amount_used = I256::from_raw(U256::from(1098120));

        assert_eq!(
            result.amount0_delta, expected_amount_out,
            "Rust swap amount1_out does not match JS amountOut"
        );
        assert_eq!(
            result.amount1_delta, expected_amount_used,
            "Rust swap amount1_out does not match JS amountOut"
        );

        // The Rust implementation accumulates fees separately; in the JS log
        // we only have `amountUsed`, which is the total input consumed.
        // We can at least assert that the total effective input (amount_used)
        // is consistent: amount_used = amount_specified - remaining.
        // In the Rust swap, that is encoded in amount0/amount1 deltas, but for
        // this test we primarily care about the output side equality.
    }
}
