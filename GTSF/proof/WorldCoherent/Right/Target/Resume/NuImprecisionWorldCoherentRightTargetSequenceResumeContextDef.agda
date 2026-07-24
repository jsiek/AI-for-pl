module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeContextDef
  where

-- File Charter:
--   * Defines contextual resumption of target sequence administration after
--     the shared inner target catch-up and the double-cast continuation.
--   * Exposes the target-context equation and target-only lineage prefix for
--     both inputs and the resumed complete catch-up result.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ-syntax)

open import Coercions using (Coercion; _︔_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import Types using (Ty; TyCtx)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( resultCtx
  ; resultStore
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageStore)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


WorldCoherentRightTargetSequenceResumeContextᵀ : Set₁
WorldCoherentRightTargetSequenceResumeContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A B C : Ty} {s t : Coercion}
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
  let s⁺ = applyCoercions (targetTailChanges result) s
      t⁺ = applyCoercions (targetTailChanges result) t
  in
  (continued : WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult result}
    {M′ = (targetResult result ⟨ s⁺ ⟩) ⟨ t⁺ ⟩}
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
      {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ} q ]
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
