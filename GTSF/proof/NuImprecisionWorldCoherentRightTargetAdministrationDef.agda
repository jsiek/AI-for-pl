module
  proof.NuImprecisionWorldCoherentRightTargetAdministrationDef
  where

-- File Charter:
--   * Defines direct execution of one hereditary target-administration plan
--     after the framed target subterm has caught up to a value.
--   * Keeps the original outer QTI derivation and the completed inner
--     catch-up explicit so active root steps can extend that same result.
--   * Returns the existing complete right-value catch-up payload directly;
--     it defines no administration-specific result or outcome carrier.
--   * Contains no implementation, postulate, hole, or permissive option.

open import Data.List using ([])

open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _∣_∣_⊢_∶_=⇒_
  )
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionTargetAdministrationPlanDef using
  (TargetAdministrationPlan)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


WorldCoherentRightTargetAdministrationᵀ : Set₁
WorldCoherentRightTargetAdministrationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B C : Ty} {c : Coercion} {μ : ModeEnv}
    {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B =⇒ C}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ c ⟩) →
  Value V →
  No• V →
  TargetAdministrationPlan ρ₀ A c⊢ p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⟨ c ⟩ ⦂ A ⊑ C ∶ q →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ⁺} q
