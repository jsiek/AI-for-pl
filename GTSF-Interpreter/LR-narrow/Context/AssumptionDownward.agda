module LR-narrow.Context.AssumptionDownward where

-- File Charter:
--   * Proves one-step downward closure of assumption-related values.
--   * Uses only the downward-closure certificate stored in the selected atom.
--   * Contains exactly one exported theorem.

open import Data.Nat using (suc)

open import LR-narrow.Atoms using
  (Atom; AtomHolds; atom-holds; relation-downward)
open import LR-narrow.LogicalRelation using
  (AssumptionRelated; paired-payload; right-sealed-payload)
open import LR-narrow.World using (Interpretation; World)

assumption-related-downward : ∀
    {assumption Φ Δᴸ Δᴿ} {w : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} w}
    {a : Atom assumption} {n V V′}
  → AssumptionRelated I a (suc n) V V′
  → AssumptionRelated I a n V V′
assumption-related-downward {a = a}
    (paired-payload left-name right-name (atom-holds related)) =
  paired-payload left-name right-name
    (atom-holds (relation-downward a related))
assumption-related-downward {a = a}
    (right-sealed-payload right-name (atom-holds related)) =
  right-sealed-payload right-name
    (atom-holds (relation-downward a related))
