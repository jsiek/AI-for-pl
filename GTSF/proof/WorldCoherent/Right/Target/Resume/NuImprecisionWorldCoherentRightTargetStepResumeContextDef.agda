module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeContextDef
  where

-- File Charter:
--   * Defines active target-step resumption with target-only context and store
--     lineage exposed in the conclusion.
--   * Reuses the existing complete catch-up carrier and adds only flat
--     equality and prefix witnesses.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; Σ-syntax)

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTys; keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )
open import proof.Core.Properties.ReductionProperties using (applyCoercions)


WorldCoherentRightTargetStepResumeContextᵀ : Set₁
WorldCoherentRightTargetStepResumeContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B C : Ty} {c : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ} p) →
  let indexed = rightCatchupIndexedResult
        (worldRightCatchupResult inner)
      result = weakIndexedResult indexed
  in
  resultCtx result ≡
    applyRightImpCtxChanges (targetTailChanges result) Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore result) →
  let c⁺ = applyCoercions (targetTailChanges result) c
  in
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ sourceResult result ⊑ targetResult result ⟨ c⁺ ⟩
    ⦂ applyTys (sourceChanges result) A
      ⊑ applyTys (targetTailChanges result) C
    ∶ transportType result q →
  ∀ {N′} →
  targetResult result ⟨ c⁺ ⟩ —→[ keep ] N′ →
  (continued : WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult result}
    {M′ = N′}
    {ρ = resultStore result}
    (transportType result q)) →
  let continued-indexed = rightCatchupIndexedResult
        (worldRightCatchupResult continued)
      continued-result = weakIndexedResult continued-indexed
  in
  resultCtx continued-result ≡
    applyRightImpCtxChanges
      (targetTailChanges continued-result)
      (resultCtx result) →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage continued))
    (resultStore continued-result) →
  Σ[ resumed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ} q ]
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
