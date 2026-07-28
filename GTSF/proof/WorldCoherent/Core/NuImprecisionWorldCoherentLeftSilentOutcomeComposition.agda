module
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  where

-- File Charter:
--   * Composes a world-coherent left-silent indexed prefix with an arbitrary
--     target-oriented world-coherent one-step outcome.
--   * Preserves generic indexed transport, type coherence, relational-store
--     lineage, and every successor-world invariant on related branches.
--   * Prepends the silent source trace directly on source-blame branches.
--   * Contains no recursive catch-up dispatcher, postulate, hole, permissive
--     option, or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
import Relation.Binary.HeterogeneousEquality as HE
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChange; keep)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import proof.Core.Properties.ReductionProperties using (↠-trans)
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( weak-one-step-compose-type-to-nested≅
  ; weak-one-step-prepend-left-silent-preserves-transportᵀ
  ; weak-one-step-prepend-left-silent-preserves-type-coherenceᵀ
  ; weak-one-step-prepend-left-silentᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( weak-one-step-index-resultᵀ
  ; weak-one-step-reindex-preserves-transportᵀ
  ; weak-one-step-reindex-preserves-type-coherenceᵀ
  ; weak-one-step-reindexᵀ
  )
open import proof.Core.Equality.HeterogeneousEqualityTransport using
  ( subst²-to-≅
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; left-silent
  ; left-silent-indexed
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; resultType
  ; silentIndexedResult
  ; sourceCatchup
  ; sourceResult
  ; sourceTypeResult
  ; targetTypeResult
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( WeakOneStepStoreLineage
  ; lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageProof
  using (weak-one-step-prepend-left-silent-store-lineageᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentWeakOneStepIndexedOutcome
  ; world-indexed-outcome-related
  ; world-indexed-outcome-source-blame
  )


world-coherent-left-silent-then-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ N′ A B}
    {χ : StoreChange}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    (silent-indexed : LeftSilentIndexedResult
      {N = M} {V′ = M′} {ρ = ρ} p) →
  let first = weakIndexedResult (silentIndexedResult silent-indexed) in
  WeakOneStepStoreLineage first →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = sourceResult first} {N′ = N′} {χ = χ}
    {ρ = resultStore first} (transportType first p) →
  WorldCoherentWeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p
world-coherent-left-silent-then-outcomeᵀ
    (left-silent-indexed first-indexed
      (left-silent-invariant refl refl) first-runtime)
    first-lineage
    (world-indexed-outcome-source-blame source↠blame) =
  world-indexed-outcome-source-blame
    (↠-trans (sourceCatchup (weakIndexedResult first-indexed))
      source↠blame)
world-coherent-left-silent-then-outcomeᵀ {p = p}
    (left-silent-indexed first-indexed
      (left-silent-invariant refl refl) first-runtime)
    first-lineage
    (world-indexed-outcome-related
      second-indexed second-lineage coherent exclusive unique) =
  world-indexed-outcome-related
    final-indexed combined-lineage coherent exclusive unique
  where
  first-raw = weakIndexedResult first-indexed
  first =
    weak-one-step-reindexᵀ first-raw refl refl
      (canonicalIndexedResults first-indexed)
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
