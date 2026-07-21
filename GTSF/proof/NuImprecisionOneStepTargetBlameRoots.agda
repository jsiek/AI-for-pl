module proof.NuImprecisionOneStepTargetBlameRoots where

-- File Charter:
--   * Packages completed target-blame catch-up as a weak indexed one-step
--     outcome at any result index with the same source endpoint.
--   * Serves target cast and conversion root-blame cases without duplicating
--     their source trace argument.

open import Data.List using ([])
open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; indexed-outcome-source-blame
  )
open import proof.NuImprecisionTargetBlameCatchup using
  (left-catchup-target-blameᵀ)


weak-one-step-target-blame-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M A B C}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK M →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ blame ⦂ A ⊑ B ∶ p →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ) →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = blame} {χ = keep} {ρ = ρ} q
weak-one-step-target-blame-indexed-outcomeᵀ okM M⊑blame q
    with left-catchup-target-blameᵀ okM M⊑blame
weak-one-step-target-blame-indexed-outcomeᵀ okM M⊑blame q
    | χs , M↠blame =
  indexed-outcome-source-blame M↠blame
