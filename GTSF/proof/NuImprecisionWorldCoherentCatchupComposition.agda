module proof.NuImprecisionWorldCoherentCatchupComposition where

-- File Charter:
--   * Lifts silent catch-up composition to the world-coherent result layer.
--   * Takes final-world coherence from the resumed catch-up result.
--   * Contains no recursive catch-up dispatch or semantic leaf assumptions.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using (StoreImp)
open import proof.NuImprecisionCatchupPrefixSupport using
  (left-catchup-indexed-resume-silentᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; resultStore
  ; silentIndexedResult
  ; sourceResult
  ; targetResult
  ; transportType
  ; weakIndexedResult
  )
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
  WorldCoherentLeftCatchupIndexedResult
    {N = sourceResult first}
    {V′ = targetResult first}
    {ρ = resultStore first}
    (transportType first p) →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ} p
world-coherent-left-catchup-indexed-resume-silentᵀ
    silent
    (world-coherent-left-indexed-catchup second coherent) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-resume-silentᵀ silent second)
    coherent
