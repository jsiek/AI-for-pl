module
  proof.NuImprecisionWorldCoherentSourceSilentCompositionProof
  where

-- File Charter:
--   * Proves world-coherent source-silent composition from the lower-level
--     result composition capability.
--   * Uses final-world precision-index uniqueness to recover the original
--     canonical index after composition.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import Relation.Binary.PropositionalEquality using (subst)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (applyTys)
open import proof.NuImprecisionAssumptionMembershipUniquenessLemma using
  (assumption-membership-unique→precision-index-unique)
open import proof.NuImprecisionSimulationCore using
  (weak-one-step-index-resultᵀ)
open import proof.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultTargetType
  ; resultType
  ; sourceChanges
  ; sourceTypeResult
  ; targetTypeResult
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionSourceSilentCompositionDef using
  ( SourceSilentComposition
  ; sourceSilentAssumptionMembershipUnique
  ; sourceSilentChangesExact
  ; sourceSilentResult
  ; sourceSilentResultExact
  ; sourceSilentSourceNameExclusive
  ; sourceSilentStoreLineage
  ; sourceSilentTransport
  ; sourceSilentTypeCoherence
  ; sourceSilentWorldCoherent
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepResultDef
  using
  ( sourceStepAssumptionMembershipUnique
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepStoreLineage
  ; sourceStepTransport
  ; sourceStepTypeCoherence
  ; sourceStepWorldCoherent
  ; world-coherent-source-one-step-indexed
  )
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionDef
  using (WorldCoherentSourceSilentCompositionᵀ)


world-coherent-source-silent-composition-proofᵀ :
  SourceSilentComposition →
  WorldCoherentSourceSilentCompositionᵀ
world-coherent-source-silent-composition-proofᵀ
    composition first source-empty source-same first-transport
    first-coherence first-lineage second =
  world-coherent-source-one-step-indexed
    combined-indexed combined-transport combined-coherence
    combined-lineage combined-changes combined-result combined-world
    combined-exclusive combined-unique
  where
  second-indexed = sourceStepIndexedResult second
  second-result = weakIndexedResult second-indexed

  combined =
    sourceSilentResult composition first source-empty source-same
      second-result

  combined-unique =
    sourceSilentAssumptionMembershipUnique
      composition first source-empty source-same second-result
      (sourceStepAssumptionMembershipUnique second)

  combined-type-eq =
    assumption-membership-unique→precision-index-unique
      combined-unique
      (subst
        (λ T → resultCtx combined ∣ resultLeftCtx combined
          ⊢ applyTys (sourceChanges combined) _
            ⊑ T ⊣ resultRightCtx combined)
        (targetTypeResult combined)
        (subst
          (λ S → resultCtx combined ∣ resultLeftCtx combined
            ⊢ S ⊑ resultTargetType combined
              ⊣ resultRightCtx combined)
          (sourceTypeResult combined)
          (resultType combined)))
      (transportType combined _)

  combined-indexed =
    weak-one-step-index-resultᵀ combined combined-type-eq

  combined-transport =
    sourceSilentTransport composition first source-empty source-same
      second-result first-transport (sourceStepTransport second)

  combined-coherence =
    sourceSilentTypeCoherence composition first source-empty source-same
      second-result first-coherence (sourceStepTypeCoherence second)

  combined-lineage =
    sourceSilentStoreLineage composition first source-empty source-same
      second-result first-lineage (sourceStepStoreLineage second)

  combined-changes =
    sourceSilentChangesExact composition first source-empty source-same
      second-result (sourceStepChangesExact second)

  combined-result =
    sourceSilentResultExact composition first source-empty source-same
      second-result (sourceStepResultExact second)

  combined-world =
    sourceSilentWorldCoherent composition first source-empty source-same
      second-result (sourceStepWorldCoherent second)

  combined-exclusive =
    sourceSilentSourceNameExclusive
      composition first source-empty source-same second-result
      (sourceStepSourceNameExclusive second)
