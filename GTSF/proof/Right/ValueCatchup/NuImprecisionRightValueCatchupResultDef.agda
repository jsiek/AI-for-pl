module proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef where

-- File Charter:
--   * Defines the recursive result retained by right-value catch-up.
--   * Keeps the source value fixed while exposing the target trace, generic
--     type transport, and canonical relation at the transported index.
--   * Contains no world invariants, implementation, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (No•; Term; Value)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedResult
  ; WeakOneStepResult
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; weakIndexedResult
  )


record RightValueCatchupIndexedResult
    {Φ Δᴸ Δᴿ V M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor right-value-indexed-catchup
  field
    rightCatchupIndexedResult :
      WeakOneStepIndexedResult
        {M = V} {N′ = M′} {χ = keep} {ρ = ρ} p

    rightCatchupSourceChangesEmpty :
      sourceChanges
        (weakIndexedResult rightCatchupIndexedResult) ≡ []

    rightCatchupSourceUnchanged :
      sourceResult
        (weakIndexedResult rightCatchupIndexedResult) ≡ V

    rightCatchupSourceValue :
      Value V

    rightCatchupSourceNoBullet :
      No• V

    rightCatchupTargetValue :
      Value
        (targetResult
          (weakIndexedResult rightCatchupIndexedResult))

    rightCatchupTargetNoBullet :
      No•
        (targetResult
          (weakIndexedResult rightCatchupIndexedResult))

open RightValueCatchupIndexedResult public
