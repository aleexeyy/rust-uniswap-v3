use thiserror::Error;

#[derive(Debug, Error)]
pub enum MathError {
    #[error("Math error - overflow")]
    Overflow,
    #[error("Math error - underflow")]
    Underflow,
    #[error("Math error - out of bounds")]
    OutOfBounds,
    #[error("Math error - division by zero")]
    DivisionByZero,
    #[error("BitMath error - zero input value")]
    ZeroValue,
}

#[derive(Debug, Error)]
pub enum StateError {
    #[error("State error - sqrtPrice out of bounds")]
    SqrtPriceOutOfBounds,
    #[error("State error - sqrtPrice is 0")]
    SqrtPriceIsZero,
    #[error("State error - sqrtRatio is 0")]
    SqrtRatioIsZero,

    #[error("State error - tick out of bounds")]
    TickOutOfBounds,

    #[error("State error - liquidity is 0")]
    LiquidityIsZero,

    #[error("State error - requested amount exceeds pool reserves")]
    InsufficientReserves,
}

#[derive(Debug, Error)]
pub enum SwapError {
    #[error("Swap error - amountSpecified must be greater than 0")]
    AmountSpecifiedIsZero,

    #[error("Swap error - sqrt price out of bounds")]
    SqrtPriceOutOfBounds,
}
#[derive(Debug, Error)]
pub enum OnchainError {
    #[error("Onchain error - failed to get tick spacing: {0}")]
    FailedToGetTickSpacing(String),

    #[error("Onchain error - failed to get slot0: {0}")]
    FailedToGetSlot0(String),

    #[error("Onchain error - failed to get liquidity: {0}")]
    FailedToGetLiquidity(String),

    #[error("Onchain error - failed to call multicall: {0}")]
    FailedToCallMulticall(String),

    #[error("Onchain error - failed decode bitmap: {0}")]
    FailedToDecodeBitmap(String),
}

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    MathError(#[from] MathError),

    #[error(transparent)]
    StateError(#[from] StateError),

    #[error(transparent)]
    SwapError(#[from] SwapError),

    #[error(transparent)]
    OnchainError(#[from] OnchainError),
}
