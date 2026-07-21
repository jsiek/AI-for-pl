module proof.NuImprecisionWorldCoherentCatchupComposition where

-- File Charter:
--   * Lifts silent catch-up composition to the world-coherent result layer.
--   * Takes final-world coherence from the resumed catch-up result.
--   * Contains no recursive catch-up dispatch or semantic leaf assumptions.

open import Agda.Builtin.Equality using (refl)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import proof.NuImprecisionCatchupPrefixSupport using
  (left-catchup-indexed-resume-silentᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; resultStore
  ; silentIndexedResult
  ; sourceResult
  ; targetResult
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionSimulationCore using
  (weak-one-step-reindexᵀ)
open import proof.NuImprecisionWeakOneStepStoreLineageDef
open import proof.NuImprecisionWeakOneStepStoreLineageProof using
  (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; world-coherent-left-indexed-catchup
  )


world-coherent-left-catchup-indexed-resume-silentᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (silent : LeftSilentIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p) →
  let first = weakIndexedResult (silentIndexedResult silent) in
  WeakOneStepStoreLineage first →
  WorldCoherentLeftCatchupIndexedResult
    {N = sourceResult first}
    {V′ = targetResult first}
    {ρ = resultStore first}
    (transportType first p) →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
world-coherent-left-catchup-indexed-resume-silentᵀ
    silent@(left-silent-indexed first-indexed
      (left-silent-invariant refl refl)
      first-runtime first-transport first-coherence)
    first-lineage
    (world-coherent-left-indexed-catchup
      second@(left-indexed-catchup second-indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        second-transport second-coherence)
      second-lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-resume-silentᵀ silent second)
    (weak-step-store-lineage
      (lineageStore combined-lineage)
      (lineageEmbedding combined-lineage)
      (lineagePrefix combined-lineage))
    coherent exclusive wfL
  where
  first-raw = weakIndexedResult first-indexed

  first = weak-one-step-reindexᵀ first-raw refl refl
    (canonicalIndexedResults first-indexed)

  first-lineage′ = weak-step-store-lineage
    (lineageStore first-lineage)
    (lineageEmbedding first-lineage)
    (lineagePrefix first-lineage)

  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      (left-silent first (left-silent-invariant refl refl))
      (weakIndexedResult second-indexed)
      first-lineage′ second-lineage
