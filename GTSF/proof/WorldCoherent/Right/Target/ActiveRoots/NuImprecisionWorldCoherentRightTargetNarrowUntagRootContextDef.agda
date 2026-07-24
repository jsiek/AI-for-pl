module
  proof.WorldCoherent.Right.Target.ActiveRoots.NuImprecisionWorldCoherentRightTargetNarrowUntagRootContextDef
  where

-- File Charter:
--   * Defines the contextual ordinary target-narrowing untag root.
--   * Consumes the constructor-specific framed relation and exposes the target
--     context action and right-only store lineage beside the complete catch-up
--     carrier.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
import Coercions as C
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTys)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ground; Ty; TyCtx; ★)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
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


WorldCoherentRightTargetNarrowUntagRootContextᵀ : Set₁
WorldCoherentRightTargetNarrowUntagRootContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A H : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ H ⊣ Δᴿ} →
  Ground H →
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
  resultCtx result
    ∣ resultLeftCtx result
    ∣ resultRightCtx result
    ∣ resultStore result ∣ []
    ⊢ᴺ sourceResult result ⊑
      targetResult result
        ⟨ applyCoercions (targetTailChanges result) (H C.？) ⟩
    ⦂ applyTys (sourceChanges result) A
      ⊑ applyTys (targetTailChanges result) H
    ∶ transportType result q →
  Σ[ resumed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′ ⟨ H C.？ ⟩} {ρ = ρ} q ]
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
