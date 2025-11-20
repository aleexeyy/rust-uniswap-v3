use crate::error::OnchainError;
use crate::swap::Slot0;
use crate::tick_math::{MAX_TICK, MIN_TICK};
use alloy::providers::Provider;
use alloy::sol;
use alloy_primitives::aliases::I24;
use alloy_primitives::{Address, BlockNumber, U160, U256};
use futures::try_join;
use rustc_hash::FxHashMap;
use std::sync::Arc;

sol! {
    #[sol(rpc)]
    interface IV3Pool {
        function tickSpacing() external view returns (int24);
        function tickBitmap(int16 wordPosition) external view returns (uint256);
        function getReserves() external view returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );
        function token0() external view returns (address);
        function token1() external view returns (address);
        function slot0() external view returns (
            uint160 sqrtPriceX96,
            int24 tick,
            uint16 observationIndex,
            uint16 observationCardinality,
            uint16 observationCardinalityNext,
            uint8 feeProtocol,
            bool unlocked
        );
        function liquidity() external view returns (uint128);
        function ticks(int24 tick) external view returns (uint128 liquidityGross, int128 liquidityNet);
    }
}

sol! {
    struct Call {
        address target;
        bytes callData;
    }

    #[sol(rpc)]
    interface IMulticall {
        function aggregate(Call[] calls)
            external
            view
            returns (uint256 blockNumber, bytes[] returnData);
    }
}

pub type OnchainProvider<P> = Arc<P>;

#[derive(Debug, Clone)]
pub struct TickInfo {
    pub word_position: i16,
    pub liquidity_gross: u128,
    pub liquidity_net: i128,
}

pub fn address_to_u160(address: Address) -> U160 {
    address.into()
}

pub fn sort_tokens(token0: Address, token1: Address) -> (Address, Address) {
    if address_to_u160(token0) < address_to_u160(token1) {
        (token0, token1)
    } else {
        (token1, token0)
    }
}

pub fn generate_search_range(current_tick: i32, tick_spacing: i32, zero_for_one: bool) -> Vec<i16> {
    let min_word: i16;
    let max_word: i16;

    if zero_for_one {
        let mut min_compressed = MIN_TICK / tick_spacing;

        if MIN_TICK % tick_spacing != 0 {
            min_compressed -= 1;
        }

        min_word = (min_compressed >> 8) as i16;

        let mut compressed = current_tick / tick_spacing;

        if current_tick < 0 && (current_tick % tick_spacing) != 0 {
            compressed -= 1;
        }
        max_word = (compressed >> 8) as i16;
    } else {
        let mut compressed = current_tick / tick_spacing;
        if current_tick < 0 && (current_tick % tick_spacing) != 0 {
            compressed -= 1;
        }
        min_word = (compressed >> 8) as i16;
        max_word = ((MAX_TICK / tick_spacing) >> 8) as i16;
    }

    (min_word..=max_word).collect()
}

#[derive(Clone, Debug)]
pub struct V3Pool<P: Provider> {
    pub pool_address: Address,
    pub token0: Address,
    pub token1: Address,
    pub fee_pips: u32,
    pub slot0: Slot0,
    pub liquidity: u128,
    pub tick_spacing: i32,
    pub bitmap: FxHashMap<i16, U256>,
    pub ticks: FxHashMap<i32, TickInfo>,
    pub contract: IV3Pool::IV3PoolInstance<OnchainProvider<P>>,
    pub multicall: IMulticall::IMulticallInstance<OnchainProvider<P>>,
    provider: OnchainProvider<P>,
}

impl<P: Provider + Send + Sync + 'static> V3Pool<P> {
    pub fn new(
        pool_address: Address,
        token0: Address,
        token1: Address,
        fee_pips: u32,
        provider: OnchainProvider<P>,
    ) -> Self {
        let (token0, token1) = sort_tokens(token0, token1);
        let contract = IV3Pool::IV3PoolInstance::new(pool_address, provider.clone());
        let multicall = IMulticall::IMulticallInstance::new(pool_address, provider.clone());
        Self {
            pool_address,
            token0,
            token1,
            fee_pips,
            slot0: Slot0::default(),
            liquidity: 0u128,
            tick_spacing: 0i32,
            bitmap: FxHashMap::default(),
            ticks: FxHashMap::default(),
            contract,
            multicall,
            provider,
        }
    }

    pub async fn fetch_tick_spacing(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<i32, OnchainError> {
        let mut call = self.contract.tickSpacing();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let tick_spacing = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetTickSpacing(e.to_string()))?;

        Ok(tick_spacing.as_i32())
    }
    pub async fn update_tick_spacing(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<i32, OnchainError> {
        self.tick_spacing = self.fetch_tick_spacing(block_number).await?;

        Ok(self.tick_spacing)
    }

    pub async fn fetch_slot0(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<Slot0, OnchainError> {
        let mut call = self.contract.slot0();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let slot0 = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetSlot0(e.to_string()))?;

        Ok(Slot0 {
            sqrt_price_x96: U256::from(slot0.sqrtPriceX96),
            tick: slot0.tick.as_i32(),
        })
    }

    pub async fn update_slot0(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<Slot0, OnchainError> {
        self.slot0 = self.fetch_slot0(block_number).await?;
        Ok(self.slot0)
    }

    pub async fn fetch_liquidity(
        &self,
        block_number: Option<BlockNumber>,
    ) -> Result<u128, OnchainError> {
        let mut call = self.contract.liquidity();

        if let Some(bn) = block_number {
            call = call.block(bn.into());
        }

        let liquidity = call
            .call()
            .await
            .map_err(|e| OnchainError::FailedToGetLiquidity(e.to_string()))?;
        Ok(liquidity)
    }

    pub async fn get_liquidity(
        &mut self,
        block_number: Option<BlockNumber>,
    ) -> Result<u128, OnchainError> {
        self.liquidity = self.fetch_liquidity(block_number).await?;

        Ok(self.liquidity)
    }

    pub async fn get_liquidity_latest(&mut self) -> Result<u128, OnchainError> {
        self.get_liquidity(None).await
    }

    pub async fn update_slot0_latest(&mut self) -> Result<Slot0, OnchainError> {
        self.update_slot0(None).await
    }

    pub async fn update_tick_spacing_latest(&mut self) -> Result<i32, OnchainError> {
        self.update_tick_spacing(None).await
    }

    pub async fn refresh_latest(&mut self) -> Result<(), OnchainError> {
        let (liq, slot0, spacing) = try_join!(
            self.fetch_liquidity(None),
            self.fetch_slot0(None),
            self.fetch_tick_spacing(None),
        )?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }

    pub async fn refresh(&mut self, block_number: Option<BlockNumber>) -> Result<(), OnchainError> {
        let (liq, slot0, spacing) = try_join!(
            self.fetch_liquidity(block_number),
            self.fetch_slot0(block_number),
            self.fetch_tick_spacing(block_number),
        )?;

        self.liquidity = liq;
        self.slot0 = slot0;
        self.tick_spacing = spacing;

        Ok(())
    }

    pub async fn fetch_batch_bitmaps(
        &self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<FxHashMap<i16, U256>, OnchainError> {
        let mut bitmap_calls: Vec<Call> = Vec::new();

        for wp in word_positions {
            let call_data = self.contract.tickBitmap(*wp).calldata().to_owned();
            bitmap_calls.push(Call {
                target: self.pool_address,
                callData: call_data,
            });
        }

        let mut agg = self.multicall.aggregate(bitmap_calls);

        if let Some(bn) = block_number {
            agg = agg.block(bn.into());
        }
        let bitmap_data = agg
            .call()
            .await
            .map_err(|e| OnchainError::FailedToCallMulticall(e.to_string()))?;

        let mut bitmaps: FxHashMap<i16, U256> = FxHashMap::default();

        for (i, raw) in bitmap_data.returnData.into_iter().enumerate() {
            let decoded = self
                .contract
                .tickBitmap(word_positions[i])
                .decode_output(raw)
                .map_err(|e| OnchainError::FailedToDecodeBitmap(e.to_string()))?;

            let bitmap = U256::from(decoded);

            if !bitmap.is_zero() {
                bitmaps.insert(word_positions[i], bitmap);
            }
        }

        Ok(bitmaps)
    }

    pub async fn fetch_ticks_for_bitmaps(
        &self,
        word_positions: &[i16],
        bitmaps: &FxHashMap<i16, U256>,
        block_number: Option<BlockNumber>,
    ) -> Result<FxHashMap<i32, TickInfo>, OnchainError> {
        let mut tick_calls: Vec<Call> = Vec::new();
        let mut tick_indices: Vec<i32> = Vec::new();
        let mut tick_word_positions: Vec<i16> = Vec::new();

        for &wp in word_positions {
            if let Some(bitmap) = bitmaps.get(&wp) {
                for bit in 0..256 {
                    // Check if bit is set
                    if (*bitmap & (U256::ONE << bit)) == U256::ZERO {
                        continue;
                    }

                    let compressed: i32 = (wp as i32) * 256 + bit;
                    let tick_index: i32 = compressed * self.tick_spacing;

                    tick_indices.push(tick_index);
                    tick_word_positions.push(wp);

                    let call_data = self
                        .contract
                        .ticks(I24::try_from(tick_index).unwrap())
                        .calldata()
                        .to_owned();
                    tick_calls.push(Call {
                        target: self.pool_address,
                        callData: call_data,
                    });
                }
            }
        }

        // nothing initialized – early exit
        if tick_calls.is_empty() {
            return Ok(FxHashMap::default());
        }

        let mut agg = self.multicall.aggregate(tick_calls);

        if let Some(bn) = block_number {
            agg = agg.block(bn.into());
        }

        let return_data = agg
            .call()
            .await
            .map_err(|e| OnchainError::FailedToCallMulticall(e.to_string()))?;

        let mut ticks: FxHashMap<i32, TickInfo> = FxHashMap::default();

        for (i, raw) in return_data.returnData.into_iter().enumerate() {
            let tick_index = tick_indices[i];
            let wp = tick_word_positions[i];

            // Assuming: ticks(int24) returns (u128 liquidityGross, i128 liquidityNet, ...)
            let decoded = self
                .contract
                .ticks(I24::try_from(tick_index).unwrap())
                .decode_output(raw)
                .map_err(|e| OnchainError::FailedToDecodeTick(e.to_string()))?;

            let liquidity_gross = decoded.liquidityGross;
            let liquidity_net = decoded.liquidityNet;

            if liquidity_gross != 0 {
                ticks.insert(
                    tick_index,
                    TickInfo {
                        word_position: wp,
                        liquidity_gross,
                        liquidity_net,
                    },
                );
            }
        }

        Ok(ticks)
    }

    pub async fn fetch_bitmaps_and_ticks(
        &self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<(FxHashMap<i16, U256>, FxHashMap<i32, TickInfo>), OnchainError> {
        // 1) fetch bitmaps
        let bitmaps = self
            .fetch_batch_bitmaps(word_positions, block_number)
            .await?;

        // 2) fetch per-tick liquidity for initialized bits
        let ticks = self
            .fetch_ticks_for_bitmaps(word_positions, &bitmaps, block_number)
            .await?;

        Ok((bitmaps, ticks))
    }

    pub async fn update_bitmaps_and_ticks(
        &mut self,
        word_positions: &[i16],
        block_number: Option<BlockNumber>,
    ) -> Result<(), OnchainError> {
        let (bitmaps, ticks) = self
            .fetch_bitmaps_and_ticks(word_positions, block_number)
            .await?;

        self.bitmap = bitmaps;
        self.ticks = ticks;

        Ok(())
    }

    pub async fn update_bitmaps_and_ticks_latest(
        &mut self,
        word_positions: &[i16],
    ) -> Result<(), OnchainError> {
        let (bitmaps, ticks) = self.fetch_bitmaps_and_ticks(word_positions, None).await?;

        self.bitmap = bitmaps;
        self.ticks = ticks;

        Ok(())
    }

    pub fn get_liquidity_net(&self, tick: &i32) -> Option<i128> {
        self.ticks.get(tick).map(|tick_info| tick_info.liquidity_net)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy::providers::{Provider, ProviderBuilder};
    use alloy::transports::mock::Asserter;
    use alloy_primitives::address;

    // mock provider for tests
    pub fn mock_provider() -> Arc<impl Provider> {
        let asserter = Asserter::new();
        let provider = ProviderBuilder::new().connect_mocked_client(asserter.clone());
        let provider = Arc::new(provider);
        provider
    }

    // --- Pure helpers: address_to_u160 & sort_tokens -----------------------------

    #[test]
    fn address_to_u160_roundtrip_like() {
        let addr = address!("0x123400000000000000000000000000000000abcd");
        let as_u160: U160 = address_to_u160(addr);

        // Converting back should give the same low 20 bytes
        let back: Address = Address::from(as_u160);
        assert_eq!(addr, back);
    }

    #[test]
    fn sort_tokens_orders_by_numeric_value() {
        let a = address!("0x0000000000000000000000000000000000000001");
        let b = address!("0x0000000000000000000000000000000000000002");

        // already sorted
        let (t0, t1) = sort_tokens(a, b);
        assert_eq!(t0, a);
        assert_eq!(t1, b);

        // reversed input still sorts
        let (t0, t1) = sort_tokens(b, a);
        assert_eq!(t0, a);
        assert_eq!(t1, b);
    }

    #[test]
    fn sort_tokens_handles_equal_addresses() {
        let a = address!("0x0000000000000000000000000000000000000001");
        let (t0, t1) = sort_tokens(a, a);

        // With equal addresses, result must still be the same pair (a, a)
        assert_eq!(t0, a);
        assert_eq!(t1, a);
    }

    // --- generate_search_range ---------------------------------------------------

    #[test]
    fn generate_search_range_is_symmetric_and_contiguous() {
        let current_tick: i32 = 13;
        let tick_spacing: i32 = 10;
        let zero_for_one: bool = false;

        let range = generate_search_range(current_tick, tick_spacing, zero_for_one);

        assert_eq!(range.len(), 347);

        assert_eq!(*range.first().unwrap(), 0);
        assert_eq!(*range.last().unwrap(), 346);
    }
    // --- V3Pool::new ------------------------------------------------------------

    #[test]
    fn v3pool_new_sorts_token_addresses_and_initializes_state() {
        let pool_address = address!("0x1000000000000000000000000000000000000000");
        let token_hi = address!("0x0000000000000000000000000000000000000002");
        let token_lo = address!("0x0000000000000000000000000000000000000001");

        let pool = V3Pool::new(pool_address, token_hi, token_lo, 3000, mock_provider());

        // basic field checks
        assert_eq!(pool.pool_address, pool_address);
        // token0/token1 sorted numerically, regardless of input order
        assert_eq!(pool.token0, token_lo);
        assert_eq!(pool.token1, token_hi);
        assert_eq!(pool.fee_pips, 3000);

        // initial state
        assert_eq!(pool.liquidity, 0);
        assert_eq!(pool.tick_spacing, 0);
        assert_eq!(pool.slot0.sqrt_price_x96, U256::ZERO);
        assert_eq!(pool.slot0.tick, 0);
        assert_eq!(pool.bitmap, FxHashMap::default());
    }
}
