module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueProof
  where

-- File Charter:
--   * Catches the source argument for target function-cast beta after the
--     source function has become a value.
--   * Frames the silent argument catch-up under both related functions and
--     preserves transport, type coherence, lineage, and cast-spine rank.
--   * Contains no semantic recursion, postulate, hole, permissive option,
--     catch-all, or compatibility wrapper.

import Coercions as C
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using
  ( inj₁
  ; inj₂
  )
open import Relation.Binary.PropositionalEquality using (trans)
open import NuTerms using
  ( no•-·
  ; ok-no
  ; _⟨_⟩
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationCore using
  ( ·₂-blame-tail
  ; weak-one-step-·₂-indexed-frameᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionWeakOneStepResultTransport
  using
  ( weak-result-transport-arrow-termsᵀ
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftSilentIndexedResult
  ; canonicalIndexedResults
  ; catchupIndexedInvariant
  ; catchupIndexedResult
  ; left-silent-indexed
  ; left-silent-invariant
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; targetIsUnchanged
  ; targetTailIsEmpty
  ; weakIndexedResult
  ; weakIndexedTransport
  ; weakIndexedTypeCoherence
  )
open import
  proof.Core.Properties.ReductionProperties
  using
  ( applyTerms-preserves-No•
  ; applyTerms-preserves-Value
  )
open import
  proof.DGG.Core.NuPreservation
  using
  (value-runtime-No•)
open import proof.Core.Properties.NuRuntimeProperties using
  (runtime-·₁; runtime-·₂)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof
  using (target-function-cast-spine-rank-applyTerms)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationFunctionCastBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
  ; WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ :
  ∀ {n} →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationFunctionCastBetaValuesAtᵀ n →
  WorldCoherentRightOneStepApplicationFunctionCastBetaSourceFunctionValueAtᵀ
    n
world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {V′ = V′} {W′ = W′} {e = e} {f = f}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ rank
    with catchup coherent exclusive unique wfL
      (runtime-·₂ vL okM)
      vW′
      (value-runtime-No• vW′
        (runtime-·₂ (vV′ ⟨ e C.↦ f ⟩) okM′))
      argument-related
world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {V′ = V′} {W′ = W′} {e = e} {f = f}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {V′ = V′} {W′ = W′} {e = e} {f = f}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₂ refl =
  world-indexed-outcome-source-blame
    (·₂-blame-tail vL source-function-no
      (sourceCatchup
        (weakIndexedResult (catchupIndexedResult caught))))
  where
  source-function-no =
    value-runtime-No• vL (runtime-·₁ okM)
world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {V′ = V′} {W′ = W′} {e = e} {f = f}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vM , noM)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
world-coherent-right-one-step-application-function-cast-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {V′ = V′} {W′ = W′} {e = e} {f = f}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ vW′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vM , noM) | refl | refl =
  world-coherent-left-silent-then-outcomeᵀ
    framed-silent framed-lineage final-outcome
  where
  caught-indexed = catchupIndexedResult caught
  caught-raw = weakIndexedResult caught-indexed

  source-function-no =
    value-runtime-No• vL (runtime-·₁ okM)
  target-function-value = vV′ ⟨ e C.↦ f ⟩
  target-function-no =
    value-runtime-No• target-function-value (runtime-·₁ okM′)

  framed-indexed =
    weak-one-step-·₂-indexed-frameᵀ
      vL source-function-no
      target-function-value target-function-no
      function-related caught-indexed
      (weakIndexedTransport caught-indexed)
      (weakIndexedTypeCoherence caught-indexed)
  framed-raw = weakIndexedResult framed-indexed

  transported-function-value =
    applyTerms-preserves-Value
      (sourceChanges caught-raw) vL
  transported-function-no =
    applyTerms-preserves-No•
      (sourceChanges caught-raw) source-function-no

  framed-silent : LeftSilentIndexedResult _
  framed-silent =
    left-silent-indexed framed-indexed
      (left-silent-invariant refl refl)
      (ok-no (no•-· transported-function-no noM))

  framed-lineage =
    weak-step-store-lineage
      (lineageStore caught-lineage)
      (lineageEmbedding caught-lineage)
      (lineagePrefix caught-lineage)

  transported-rank =
    trans
      (target-function-cast-spine-rank-applyTerms
        (sourceChanges caught-raw) vL)
      rank

  final-outcome =
    terminal
      final-coherent final-exclusive final-unique final-wfL
      (ok-no (no•-· transported-function-no noM))
      okM′
      (weak-result-transport-arrow-termsᵀ
        caught-raw
        (weakIndexedTransport caught-indexed)
        (weakIndexedTypeCoherence caught-indexed)
        source-function-no target-function-no function-related)
      (canonicalIndexedResults caught-indexed)
      transported-function-value vM vV′ vW′ transported-rank
