module
  proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeMap
  where

-- File Charter:
--   * Maps a recursive source-step outcome through a term frame.
--   * Accepts separate maps for the exact continuing result and the source
--     blame trace, so source and target frames share one exhaustive proof.
--   * Contains no recursive worker, postulate, hole, or permissive option.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Data.Product using (_,_; ∃-syntax)
open import NuReduction using (StoreChange; _—↠[_]_)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term; blame)
open import Types using (Ty; TyCtx)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepOutcomeDef using
  ( WorldCoherentSourceOneStepOutcome
  ; source-step-outcome-related
  ; source-step-outcome-source-blame
  )
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


world-coherent-source-one-step-outcome-mapᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {χ : StoreChange}
    {M M′ L N N′ K : Term} {A B C D : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ} →
  (WorldCoherentSourceOneStepIndexedResult
      {M = M} {M′ = M′} {L = L}
      {χ = χ} {ρ = ρ} p →
    WorldCoherentSourceOneStepIndexedResult
      {M = N} {M′ = N′} {L = K}
      {χ = χ} {ρ = ρ} q) →
  (∀ {χs} → M —↠[ χs ] blame →
    ∃[ ψs ] (N —↠[ ψs ] blame)) →
  WorldCoherentSourceOneStepOutcome
    {M = M} {M′ = M′} {L = L}
    {χ = χ} {ρ = ρ} p →
  WorldCoherentSourceOneStepOutcome
    {M = N} {M′ = N′} {L = K}
    {χ = χ} {ρ = ρ} q
world-coherent-source-one-step-outcome-mapᵀ
    related-frame blame-frame
    (source-step-outcome-related result) =
  source-step-outcome-related (related-frame result)
world-coherent-source-one-step-outcome-mapᵀ
    related-frame blame-frame
    (source-step-outcome-source-blame source↠blame)
    with blame-frame source↠blame
world-coherent-source-one-step-outcome-mapᵀ
    related-frame blame-frame
    (source-step-outcome-source-blame source↠blame)
    | ψs , framed-source↠blame =
  source-step-outcome-source-blame framed-source↠blame
