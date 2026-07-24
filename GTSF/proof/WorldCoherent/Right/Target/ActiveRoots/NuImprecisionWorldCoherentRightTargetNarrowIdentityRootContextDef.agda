module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowIdentityRootContextDef
  where

-- File Charter:
--   * Defines the contextual target-narrowing identity-root leaf.
--   * Covers the three active atomic identity forms and exposes the target
--     context action and right-only store lineage beside the existing complete
--     catch-up carrier.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (ModeEnv; id)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
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
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetNarrowIdentityRootContextᵀ : Set₁
WorldCoherentRightTargetNarrowIdentityRootContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B : Ty} {μ : ModeEnv}
    {p q : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK (M′ ⟨ id B ⟩) →
  Value V →
  No• V →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ id B ∶ B ⊒ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ V ⊑ M′ ⦂ A ⊑ B ∶ p →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))
    ≡
    applyRightImpCtxChanges
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult inner))))
      Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))) →
  Σ[ resumed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ id B ⟩} {ρ = ρ⁺} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult resumed)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult resumed))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage resumed))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult resumed))))
