module proof.NuImprecisionWorldCoherentSourceOneStepProof where

-- File Charter:
--   * Projects the exact recursive source one-step result to the compact
--     source-oriented engine consumed by forward DGG trace induction.
--   * Erases generic transport and store lineage only after checking the
--     exact distinguished source change and result term.
--   * Contains no recursive simulation implementation, postulate, or hole.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

open import proof.NuImprecisionSimulationResultDef using
  ( canonicalIndexedResults
  ; resultCtx
  ; resultStore
  ; sourceCtxResult
  ; sourceStoreResult
  ; targetCtxResult
  ; targetResult
  ; targetStoreResult
  ; targetTail
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import proof.NuImprecisionWorldCoherentSourceOneStepDef using
  (WorldCoherentSourceOneStepSimulationᵀ)
open import proof.NuImprecisionWorldCoherentSourceOneStepResultDef using
  ( WorldCoherentExactSourceOneStepSimulationᵀ
  ; sourceStepChangesExact
  ; sourceStepIndexedResult
  ; sourceStepResultExact
  ; sourceStepSourceNameExclusive
  ; sourceStepWorldCoherent
  )


world-coherent-source-one-step-proofᵀ :
  WorldCoherentExactSourceOneStepSimulationᵀ →
  WorldCoherentSourceOneStepSimulationᵀ
world-coherent-source-one-step-proofᵀ
    exact-step {p = p} coherent exclusive wfL wfR
    okM okM′ M⊑M′ source-step
    with exact-step coherent exclusive wfL wfR okM okM′ M⊑M′
      source-step
world-coherent-source-one-step-proofᵀ
    exact-step {p = p} coherent exclusive wfL wfR
    okM okM′ M⊑M′ source-step
    | exact-result
    with sourceCtxResult result
       | targetCtxResult result
       | sourceStepChangesExact exact-result
       | sourceStepResultExact exact-result
  where
  indexed = sourceStepIndexedResult exact-result
  result = weakIndexedResult indexed
world-coherent-source-one-step-proofᵀ
    exact-step {p = p} coherent exclusive wfL wfR
    okM okM′ M⊑M′ source-step
    | exact-result | refl | refl | refl | refl =
      targetResult result ,
      targetTailChanges result ,
      resultCtx result ,
      resultStore result ,
      transportType result p ,
      targetTail result ,
      sourceStepWorldCoherent exact-result ,
      sourceStepSourceNameExclusive exact-result ,
      sourceStoreResult result ,
      targetStoreResult result ,
      canonicalIndexedResults indexed
  where
  indexed = sourceStepIndexedResult exact-result
  result = weakIndexedResult indexed
