module proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition where

-- File Charter:
--   * Lifts silent catch-up composition to the world-coherent result layer.
--   * Takes final-world coherence from the resumed catch-up result.
--   * Contains no recursive catch-up dispatch or semantic leaf assumptions.

open import Agda.Builtin.Equality using (refl)
import Relation.Binary.HeterogeneousEquality as HE
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp)
open import proof.Catchup.Core.NuImprecisionCatchupPrefixSupport using
  (left-catchup-indexed-resume-silentᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftCatchupIndexedResult
  ; LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; resultSourceType
  ; resultTargetType
  ; resultType
  ; silentIndexedResult
  ; sourceResult
  ; sourceTypeResult
  ; targetResult
  ; targetTypeResult
  ; transportType
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  ; weakIndexedResult
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( subst²-to-≅
  ; weak-one-step-compose-type-to-nested≅
  ; weak-one-step-index-resultᵀ
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silentᵀ
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  )
open import
  proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef
  using (rightCatchupIndexedResult)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof using
  (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  ( WorldCoherentLeftCatchupIndexedResult
  ; WorldCoherentWeakOneStepIndexedOutcome
  ; world-coherent-left-indexed-catchup
  ; world-indexed-outcome-related
  )
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; world-coherent-right-value-indexed-catchup
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
      first-runtime)
    first-lineage
    (world-coherent-left-indexed-catchup
      second@(left-indexed-catchup second-indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      second-lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-resume-silentᵀ silent second)
    (weak-step-store-lineage
      (lineageStore combined-lineage)
      (lineageEmbedding combined-lineage)
      (lineagePrefix combined-lineage))
    coherent exclusive unique wfL
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


world-coherent-left-silent-then-right-valueᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    (silent-indexed : LeftSilentIndexedResult
      {N = M} {V′ = M′} {ρ = ρ} p) →
  let first = weakIndexedResult (silentIndexedResult silent-indexed) in
  WeakOneStepStoreLineage first →
  WorldCoherentRightValueCatchupIndexedResult
    {V = sourceResult first}
    {M′ = N′}
    {ρ = resultStore first}
    (transportType first p) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = keep} {ρ = ρ} p
world-coherent-left-silent-then-right-valueᵀ {p = p}
    (left-silent-indexed first-indexed
      (left-silent-invariant refl refl) first-runtime)
    first-lineage
    (world-coherent-right-value-indexed-catchup
      second-catchup second-lineage second-bullet
      final-coherent final-exclusive final-unique final-wfR) =
  world-indexed-outcome-related
    final-indexed
    combined-lineage
    final-coherent final-exclusive final-unique
  where
  first-raw = weakIndexedResult first-indexed
  first =
    weak-one-step-reindexᵀ first-raw refl refl
      (canonicalIndexedResults first-indexed)
  second-indexed = rightCatchupIndexedResult second-catchup
  second-raw = weakIndexedResult second-indexed
  second =
    weak-one-step-reindexᵀ second-raw refl refl
      (canonicalIndexedResults second-indexed)
  silent = left-silent first (left-silent-invariant refl refl)
  combined = weak-one-step-prepend-left-silentᵀ silent second

  first-lineage′ =
    weak-step-store-lineage
      (lineageStore first-lineage)
      (lineageEmbedding first-lineage)
      (lineagePrefix first-lineage)
  second-lineage′ =
    weak-step-store-lineage
      (lineageStore second-lineage)
      (lineageEmbedding second-lineage)
      (lineagePrefix second-lineage)
  combined-lineage =
    weak-one-step-prepend-left-silent-store-lineageᵀ
      silent second first-lineage′ second-lineage′

  combined-transport =
    weak-one-step-prepend-left-silent-preserves-transportᵀ
      silent second
      (weak-one-step-reindex-preserves-transportᵀ
        first-raw refl refl
        (canonicalIndexedResults first-indexed)
        (weakIndexedTransport first-indexed))
      (weak-one-step-reindex-preserves-transportᵀ
        second-raw refl refl
        (canonicalIndexedResults second-indexed)
        (weakIndexedTransport second-indexed))

  combined-coherence =
    weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
      silent second
      (weak-one-step-reindex-preserves-type-coherenceᵀ
        first-raw refl refl
        (canonicalIndexedResults first-indexed)
        (weakIndexedTypeCoherence first-indexed))
      (weak-one-step-reindex-preserves-type-coherenceᵀ
        second-raw refl refl
        (canonicalIndexedResults second-indexed)
        (weakIndexedTypeCoherence second-indexed))

  type-eq =
    HE.≅-to-≡
      (HE.trans
        (subst²-to-≅
          {P = λ S T →
            resultCtx combined ∣ resultLeftCtx combined
              ⊢ S ⊑ T ⊣ resultRightCtx combined}
          (sourceTypeResult combined)
          (targetTypeResult combined)
          (resultType combined))
        (HE.sym
          (weak-one-step-compose-type-to-nested≅
            first second p)))

  final-indexed =
    weak-one-step-index-resultᵀ
      combined type-eq combined-transport combined-coherence
