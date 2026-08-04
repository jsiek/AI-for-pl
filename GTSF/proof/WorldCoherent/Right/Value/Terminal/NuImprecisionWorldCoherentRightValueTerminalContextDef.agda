module
  proof.WorldCoherent.Right.Value.Terminal.NuImprecisionWorldCoherentRightValueTerminalContextDef
  where

-- File Charter:
--   * Defines the contextual zero-step terminal seed for recursive
--     right-value catch-up.
--   * Exposes both the unchanged imprecision context and the reflexive
--     target-only lineage prefix inline with the existing catch-up carrier.
--   * Contains no implementation, result/view/outcome hierarchy, postulate,
--     hole, permissive option, or broad simulation import.

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
open import NuTerms using (No•; Term; Value)
open import QuotientedTermImprecision using
  (StoreImpPrefix; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
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
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightValueTerminalContextᵀ : Set₁
WorldCoherentRightValueTerminalContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V V′ : Term} {A B : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  Value V →
  No• V →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ V′ ⦂ A ⊑ B ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = V′} {ρ = ρ⁺} p ]
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
