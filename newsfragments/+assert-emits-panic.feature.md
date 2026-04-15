`assert(false)` now reverts with a Solidity-compatible `Panic(uint256)` payload (code `0x01`) instead of empty revert data. This makes assertion failures identifiable by off-chain tooling.
