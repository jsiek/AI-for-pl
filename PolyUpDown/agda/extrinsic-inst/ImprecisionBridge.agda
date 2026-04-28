module ImprecisionBridge where

-- File Charter:
--   * Historical home of the soundness bridge from unindexed `Imprecision` to
--   * `Cast`.
--   * The old full bridge is intentionally not exported: unindexed imprecision
--   * still contains arbitrary concrete-seal precision `⊑-｀ αˡ αʳ`, while
--   * `Cast` now correctly permits only same-seal casts `｀ α ⊑ᶜ ｀ α`.
--   * The active same-seal soundness bridge lives in `ImprecisionIndexed`.

open import Types
open import Imprecision
open import Cast

