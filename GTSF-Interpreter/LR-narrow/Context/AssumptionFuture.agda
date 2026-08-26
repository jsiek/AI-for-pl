module LR-narrow.Context.AssumptionFuture where

-- File Charter:
--   * Preserves assumption-related values in a future interpretation.
--   * Uses preservation of the two runtime type environments only.
--   * Contains exactly one exported theorem.

open import Agda.Builtin.Equality using (refl)

open import LR-narrow.Atoms using (Atom)
open import LR-narrow.LogicalRelation using
  (AssumptionRelated; paired-payload; right-sealed-payload)
open import LR-narrow.World

assumption-related-future : ∀
    {assumption Φ Δᴸ Δᴿ} {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {a : Atom assumption} {n V V′}
  → J ⊒ⁱ I
  → AssumptionRelated I a n V V′
  → AssumptionRelated J a n V V′
assumption-related-future
    (future-interpretation world-future refl refl atoms-eq)
    (paired-payload left-name right-name related) =
  paired-payload left-name right-name related
assumption-related-future
    (future-interpretation world-future refl refl atoms-eq)
    (right-sealed-payload right-name related) =
  right-sealed-payload right-name related
