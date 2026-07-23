module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetStepResumeDef
  where

-- File Charter:
--   * Defines the flat boundary for resuming a right-value catch-up after one
--     active target cast step.
--   * Exposes the framed relation, target step, and already completed
--     continuation directly, using the existing catch-up carrier throughout.
--   * Supports identity, sequence, instantiation, and other active target
--     roots without introducing another result, view, or outcome hierarchy.
--   * Contains no implementation, postulate, hole, permissive option, or
--     termination bypass.

open import Data.List using ([])

open import Coercions using (Coercion)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (applyTys; keep; _—→[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultLeftCtx
  ; resultRightCtx
  ; resultCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  )
open import proof.Core.Properties.ReductionProperties using (applyCoercions)


WorldCoherentRightTargetStepResumeᵀ : Set₁
WorldCoherentRightTargetStepResumeᵀ =
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
      c⁺ = applyCoercions (targetTailChanges result) c
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
  WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult result}
    {M′ = N′}
    {ρ = resultStore result}
    (transportType result q) →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ c ⟩} {ρ = ρ} q
