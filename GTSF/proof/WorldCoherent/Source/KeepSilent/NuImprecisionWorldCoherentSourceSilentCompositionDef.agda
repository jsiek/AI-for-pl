module
  proof.WorldCoherent.Source.KeepSilent.NuImprecisionWorldCoherentSourceSilentCompositionDef
  where

-- File Charter:
--   * Defines composition of a source-silent weak result with a following
--     exact world-coherent source step.
--   * Returns the existing exact source-step result at the original index.
--   * Contains no implementation, result wrapper, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; WeakOneStepTransport
  ; WeakOneStepTypeCoherence
  ; resultSourceType
  ; resultStore
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; transportType
  )
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)
open import proof.WorldCoherent.Source.OneStep.Cases.NuImprecisionWorldCoherentSourceOneStepResultDef using
  (WorldCoherentSourceOneStepIndexedResult)


WorldCoherentSourceSilentCompositionᵀ : Set₁
WorldCoherentSourceSilentCompositionᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ L A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    (first : WeakOneStepResult ρ M M′ A B keep) →
  sourceChanges first ≡ [] →
  sourceResult first ≡ M →
  WeakOneStepTransport first →
  WeakOneStepTypeCoherence first →
  WeakOneStepStoreLineage first →
  WorldCoherentSourceOneStepIndexedResult
    {M = sourceResult first} {M′ = targetResult first} {L = L}
    {A = resultSourceType first} {B = resultTargetType first}
    {χ = χ} {ρ = resultStore first}
    (resultType first) →
  WorldCoherentSourceOneStepIndexedResult
    {M = M} {M′ = M′} {L = L}
    {A = A} {B = B} {χ = χ} {ρ = ρ} p
