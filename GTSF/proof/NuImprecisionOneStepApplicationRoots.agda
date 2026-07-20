module proof.NuImprecisionOneStepApplicationRoots where

-- File Charter:
--   * Owns nonrecursive root-reduction leaves for application cases in the
--     indexed one-step dispatcher.
--   * Currently proves target left-function blame; target right-argument
--     blame and beta roots require value catch-up and live in later stages.
--   * Exports strict outcome-level statements and contains no dispatcher
--     recursion.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_; _↦_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using
  ( RuntimeOK
  ; blame
  ; no•-·
  ; ok-no
  ; ok-·₁
  ; ok-·₂
  ; _·_
  )
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (_⇒_)
open import proof.NuImprecisionSimulationCore using
  ( WeakOneStepIndexedOutcome
  ; indexed-outcome-source-blame
  ; ·₁-blame-tail
  )
open import proof.NuImprecisionTargetBlameCatchup using
  ( left-catchup-target-blameᵀ
  ; value-not-target-blameᵀ
  )


weak-one-step-application-left-blame-indexed-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ L M A A′ B B′ pA pB}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  RuntimeOK (L · M) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ blame
    ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ↦ pB →
  WeakOneStepIndexedOutcome
    {M = L · M} {N′ = blame} {χ = keep} {ρ = ρ} pB
weak-one-step-application-left-blame-indexed-outcomeᵀ
    (ok-no (no•-· noL noM)) L⊑blame
    with left-catchup-target-blameᵀ (ok-no noL) L⊑blame
weak-one-step-application-left-blame-indexed-outcomeᵀ
    (ok-no (no•-· noL noM)) L⊑blame
    | χs , L↠blame =
  indexed-outcome-source-blame (·₁-blame-tail noM L↠blame)
weak-one-step-application-left-blame-indexed-outcomeᵀ
    (ok-·₁ okL noM) L⊑blame
    with left-catchup-target-blameᵀ okL L⊑blame
weak-one-step-application-left-blame-indexed-outcomeᵀ
    (ok-·₁ okL noM) L⊑blame
    | χs , L↠blame =
  indexed-outcome-source-blame (·₁-blame-tail noM L↠blame)
weak-one-step-application-left-blame-indexed-outcomeᵀ
    (ok-·₂ vL noL okM) L⊑blame =
  ⊥-elim (value-not-target-blameᵀ vL L⊑blame)
