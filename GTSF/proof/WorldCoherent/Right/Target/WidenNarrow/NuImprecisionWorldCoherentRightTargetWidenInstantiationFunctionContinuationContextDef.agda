module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstantiationFunctionContinuationContextDef
  where

-- File Charter:
--   * Defines contextual target-instantiation-to-function continuation after
--     the shared inner right-value catch-up.
--   * Retains the transported original precision index instead of proposing
--     a false uniform right-only opening of a matched target binder.
--   * Takes the original prefix and instantiation typing needed to transport
--     the cast through the completed inner result.
--   * Exposes target-context action and right-only store lineage for the
--     continuation in the inner result world.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; ModeEnv; inst)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (CastMode; SealModeStore★)
open import Types using
  (Ty; TyCtx; ★; _⇒_; `∀)
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


WorldCoherentRightTargetWidenInstantiationFunctionContinuationContextᵀ :
  Set₁
WorldCoherentRightTargetWidenInstantiationFunctionContinuationContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ : Term} {A C : Ty} {s : Coercion} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⇒ ★ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
    ⊢ inst (★ ⇒ ★) s ∶ `∀ C ⊑ ★ ⇒ ★ →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ⁺} p) →
  let indexed = rightCatchupIndexedResult
        (worldRightCatchupResult inner)
      result = weakIndexedResult indexed
  in
  resultCtx result ≡
    applyRightImpCtxChanges (targetTailChanges result) Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore result) →
  Σ[ continued ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = sourceResult result}
      {M′ =
        targetResult result
          ⟨ applyCoercions (targetTailChanges result)
              (inst (★ ⇒ ★) s) ⟩}
      {ρ = resultStore result}
      (transportType result q) ]
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
        (resultCtx result))
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage continued))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult continued))))
