module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsResidualAccDef
  where

-- File Charter:
--   * Defines the exact residual branch capability for the private
--     accessibility-indexed target pending-cast worker.
--   * Covers only unseal, instantiation, and the two fused eager plans; the
--     worker itself owns empty, inert, identity, untag, and sequence plans.
--   * Keeps the typed hereditary tail, recursion accessibility, and existing
--     contextual catch-up conclusion explicit.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  (Coercion; id-onlyᵈ; _∣_∣_⊢_∶_=⇒_)
open import Conversion using
  (ConcealConversion; RevealConversion)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import Data.Product using (_×_; ∃-syntax; Σ-syntax)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Induction.WellFounded using (Acc)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊒_; _∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
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
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using
  ( ResidualTargetAdministrationPlan
  ; TargetAdministrationSpine
  ; applyTargetPendingCasts
  )
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


WorldCoherentRightTargetPendingCastsResidualAccᵀ : Set₁
WorldCoherentRightTargetPendingCastsResidualAccᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V W : Term} {A B C D : Ty} {c : Coercion}
    {cs : List Coercion} {μ}
    {c⊢ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B =⇒ C}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ D ⊣ Δᴿ} →
  (vW : Value W) →
  Acc _<_ (targetPendingAdministrationRank vW (c ∷ cs)) →
  (plan : TargetAdministrationPlan ρ A c⊢ p r) →
  ResidualTargetAdministrationPlan plan →
  ((∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      RevealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c B C)
   ⊎
   (∃[ μ′ ] ∃[ β ] ∃[ X′ ]
      ConcealConversion μ′ Δᴿ (rightStoreⁱ ρ)
        β X′ c B C)
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊒ C))
   ⊎
   (∃[ μ′ ]
      CastMode μ′ ×
      SealModeStore★ μ′ (rightStoreⁱ ρ) ×
      (μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c ∶ B ⊑ C))
   ⊎
   (SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ) ×
    (id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ
      ⊢ c ∶ B ⊑ C))) →
  TargetAdministrationSpine ρ A r q cs →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK (applyTargetPendingCasts W (c ∷ cs)) →
  Value V →
  No• V →
  No• W →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ V ⊑ W ⦂ A ⊑ B ∶ p →
  Σ[ caught ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V}
      {M′ = applyTargetPendingCasts W (c ∷ cs)}
      {ρ = ρ} q ]
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
      (lineageStore (worldRightCatchupStoreLineage caught))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))
