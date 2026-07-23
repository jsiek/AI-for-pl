module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetSequenceResumeDef
  where

-- File Charter:
--   * Defines direct resumption of target sequence administration after the
--     shared inner target catch-up has reached its value.
--   * Places the administrative sequence step between that shared prefix and
--     an already completed continuation in the resulting final world.
--   * Consumes and returns only the existing complete world-coherent
--     right-value catch-up payload.
--   * Contains no implementation, auxiliary carrier, postulate, hole, or
--     permissive option.

open import Coercions using (Coercion; _︔_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; _⟨_⟩)
open import Types using (Ty; TyCtx)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultStore
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


WorldCoherentRightTargetSequenceResumeᵀ : Set₁
WorldCoherentRightTargetSequenceResumeᵀ =
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
      s⁺ = applyCoercions (targetTailChanges result) s
      t⁺ = applyCoercions (targetTailChanges result) t
  in
  WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult result}
    {M′ = (targetResult result ⟨ s⁺ ⟩) ⟨ t⁺ ⟩}
    {ρ = resultStore result}
    (transportType result q) →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′ ⟨ s ︔ t ⟩} {ρ = ρ} q
