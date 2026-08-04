module
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupContextDef
  where

-- File Charter:
--   * Defines right-value catch-up with the target-only imprecision-context
--     action exposed in its conclusion.
--   * Strengthens the ambient-prefix catch-up boundary without adding a new
--     result, view, outcome, or recursive-plan hierarchy.
--   * Contains no implementation, postulate, hole, permissive option, or
--     broad simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import NuTerms using (No•; RuntimeOK; Value)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultStore
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightValueCatchupContextᵀ : Set₁
WorldCoherentRightValueCatchupContextᵀ =
  ∀ {Φ Δᴸ Δᴿ V M′ A B}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value V →
  No• V →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρ⁺} p ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult caught))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore
        (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))
