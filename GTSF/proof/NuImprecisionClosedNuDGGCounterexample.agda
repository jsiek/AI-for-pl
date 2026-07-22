module proof.NuImprecisionClosedNuDGGCounterexample where

-- File Charter:
--   * Refutes `ClosedNuDGG` after `gen⊑groundᵀ` using a mismatched
--     target tag and untag.
--   * The source is already a value while the target deterministically
--     reaches blame, contradicting the forward value clause.
--   * Introduces no result carrier, view, wrapper, postulate, or hole.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (_,_)
open import NuReduction using (↠-refl)
open import proof.NuDGGSpine using (ClosedNuDGG)
open import
  proof.NuImprecisionGenUntagMismatchCounterexampleCore using
  ( initial-relation
  ; source-runtime
  ; sourceValue
  ; target-blame-trace
  ; target-runtime
  ; vSourceValue
  )
open import proof.NuReductionDeterminism using
  (source-blame-excludes-value)


closed-nu-dgg-mismatch-counterexample : ClosedNuDGG → ⊥
closed-nu-dgg-mismatch-counterexample dgg
    with dgg source-runtime target-runtime initial-relation
closed-nu-dgg-mismatch-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    with forward sourceValue [] ↠-refl vSourceValue
closed-nu-dgg-mismatch-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    | V′ , χs′ , Φ , ρ , r , target-trace , vV′ ,
      left-eq , right-eq , final-relation =
  source-blame-excludes-value target-blame-trace target-trace vV′
