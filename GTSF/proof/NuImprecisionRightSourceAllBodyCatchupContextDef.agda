module
  proof.NuImprecisionRightSourceAllBodyCatchupContextDef
  where

-- File Charter:
--   * Defines source-universal body catch-up with the final source-only-head
--     imprecision context exposed explicitly.
--   * Returns the existing catch-up carrier, lifted ambient store, and prefix
--     directly, without adding a result or view hierarchy.
--   * Contains no implementation, recursion, postulate, hole, permissive
--     option, or broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; ∃-syntax; Σ-syntax)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Term; Value)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultStore
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightSourceAllBodyCatchupContextᵀ : Set₁
WorldCoherentRightSourceAllBodyCatchupContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {V N′ : Term} {A B : Ty}
    {p : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK N′ →
  Value V →
  No• V →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρᴸ →
  ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ suc Δᴸ ∣ Δᴿ ∣ ρᴸ ∣ []
    ⊢ᴺ V ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∃[ ρ⁺ᴸ ]
    LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ⁺ ρ⁺ᴸ ×
    StoreImpPrefix ρᴸ ρ⁺ᴸ ×
    Σ[ caught ∈
      WorldCoherentRightValueCatchupIndexedResult
        {V = V} {M′ = N′} {ρ = ρ⁺ᴸ} p ]
      (resultCtx
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught)))
        ≡
      (zero ˣ⊑★) ∷
        ⇑ᴸᵢ
          (applyRightImpCtxChanges
            (targetTailChanges
              (weakIndexedResult
                (rightCatchupIndexedResult
                  (worldRightCatchupResult caught))))
            Φ))
      ×
      RightOnlyStoreImpPrefix
        (lineageStore
          (worldRightCatchupStoreLineage caught))
        (resultStore
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
