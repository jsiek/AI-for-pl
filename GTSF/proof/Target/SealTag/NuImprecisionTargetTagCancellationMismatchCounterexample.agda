module
  proof.Target.SealTag.NuImprecisionTargetTagCancellationMismatchCounterexample where

-- File Charter:
--   * Refutes generalized target-tag cancellation after `gen⊑groundᵀ`.
--   * Uses distinct observed and requested ground labels from the shared
--     mismatch core.
--   * Introduces no result carrier, view, wrapper, postulate, or hole.

open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import
  proof.NuCore.Misc.NuImprecisionGenUntagMismatchCounterexampleCore using
  ( nat-not-function-ground
  ; noSourceValue
  ; source-value-tagged-relation
  ; vSourceValue
  ; vWNat
  )
open import proof.NuCore.Misc.NuImprecisionGenUntagCounterexampleCore using
  (exclusive₀; gG; q; unique₀)
open import proof.Target.SealTag.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)


target-tag-cancellation-mismatch-counterexample :
  TargetTagCancellationᵀ →
  ⊥
target-tag-cancellation-mismatch-counterexample cancel
    with cancel exclusive₀ unique₀ gG vSourceValue noSourceValue
      vWNat source-value-tagged-relation q
target-tag-cancellation-mismatch-counterexample cancel
    | tag-eq , canceled =
  nat-not-function-ground tag-eq
