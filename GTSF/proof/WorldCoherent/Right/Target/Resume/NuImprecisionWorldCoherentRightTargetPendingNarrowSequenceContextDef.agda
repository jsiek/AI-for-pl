module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingNarrowSequenceContextDef
  where

-- File Charter:
--   * Defines contextual continuation of one pending target narrowing
--     sequence after its shared source and target values are known.
--   * Retains the hereditary component plans and strict rank equation needed
--     by the private target-administration SCC.
--   * Returns the existing complete catch-up carrier together with the
--     target-context equation and target-only store-lineage prefix.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (_×_; proj₁; Σ-syntax)

open import Coercions using (Coercion; ModeEnv; _︔_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
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
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef
  using (targetPendingAdministrationRank)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef
  using (TargetAdministrationPlan)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightTargetPendingNarrowSequenceContextᵀ : Set₁
WorldCoherentRightTargetPendingNarrowSequenceContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B C D : Ty} {s t : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
  (vW : Value W) →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ) →
  (s⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ B ⊒ C) →
  (t⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C ⊒ D) →
  TargetAdministrationPlan ρ A (proj₁ s⊒) p r →
  TargetAdministrationPlan ρ A (proj₁ t⊒) r q →
  targetPendingAdministrationRank vW ((s ︔ t) ∷ []) ≡
    suc (targetPendingAdministrationRank vW (s ∷ t ∷ [])) →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK ((W ⟨ s ⟩) ⟨ t ⟩) →
  Value V →
  No• V →
  No• W →
  Σ[ continued ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = (W ⟨ s ⟩) ⟨ t ⟩} {ρ = ρ} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult continued))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage continued))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued))))
