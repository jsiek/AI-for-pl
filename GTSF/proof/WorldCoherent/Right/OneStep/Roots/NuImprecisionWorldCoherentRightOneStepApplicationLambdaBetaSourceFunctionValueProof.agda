module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueProof
  where

-- File Charter:
--   * Catches a source argument up to its related target value, frames that
--     catch-up under an already-valued source function, and invokes the
--     value/value target-lambda beta terminal.
--   * Preserves generic transport, type coherence, relational-store lineage,
--     and every final-world invariant.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     or compatibility wrapper.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import Data.Sum using
  ( inj₁
  ; inj₂
  )
open import Relation.Binary.PropositionalEquality using (trans)
open import NuReduction using (keep)
open import NuTerms using
  ( no•-·
  ; ok-no
  ; ƛ_
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
  ; resultStore
  ; silentInvariant
  ; sourceCatchup
  ; sourceChanges
  ; sourceIsValueOrBlame
  ; sourceResult
  ; targetIsUnchanged
  ; targetTailIsEmpty
  ; transportNo•Terms
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentLeftSilentOutcomeComposition
  using (world-coherent-left-silent-then-outcomeᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( world-coherent-left-indexed-catchup
  ; world-indexed-outcome-source-blame
  )
open import
  proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureProof
  using (target-function-cast-spine-rank-applyTerms)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepApplicationLambdaBetaRankedDef
  using
  ( WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ
  ; WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ
  )
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ :
  ∀ {n} →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepApplicationLambdaBetaValuesAtᵀ n →
  WorldCoherentRightOneStepApplicationLambdaBetaSourceFunctionValueAtᵀ n
world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {N′ = N′} {V′ = V′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ rank
    with catchup coherent exclusive unique wfL
      (runtime-·₂ vL okM)
      vV′
      (value-runtime-No• vV′ (runtime-·₂ (ƛ N′) okM′))
      argument-related
world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {N′ = N′} {V′ = V′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    with sourceIsValueOrBlame (catchupIndexedInvariant caught)
world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {N′ = N′} {V′ = V′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ rank
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
world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {N′ = N′} {V′ = V′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW)
    with targetTailIsEmpty
           (silentInvariant (catchupIndexedInvariant caught))
       | targetIsUnchanged
           (silentInvariant (catchupIndexedInvariant caught))
world-coherent-right-one-step-application-lambda-beta-source-function-value-at-proofᵀ
    catchup terminal
    {L = L} {N′ = N′} {V′ = V′}
    coherent exclusive unique wfL okM okM′
    function-related argument-related vL vV′ rank
    | world-coherent-left-indexed-catchup
        caught caught-lineage final-coherent final-exclusive final-unique
        final-wfL
    | inj₁ (vW , noW) | refl | refl =
  world-coherent-left-silent-then-outcomeᵀ
    framed-silent framed-lineage final-outcome
  where
  caught-indexed = catchupIndexedResult caught
  caught-raw = weakIndexedResult caught-indexed

  source-function-no =
    value-runtime-No• vL (runtime-·₁ okM)
  target-function-no =
    value-runtime-No• (ƛ N′) (runtime-·₁ okM′)

  framed-indexed =
    weak-one-step-·₂-indexed-frameᵀ
      vL source-function-no
      (ƛ N′) target-function-no
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
      (ok-no (no•-· transported-function-no noW))

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
      (ok-no (no•-· transported-function-no noW))
      okM′
      (weak-result-transport-arrow-termsᵀ
        caught-raw
        (weakIndexedTransport caught-indexed)
        (weakIndexedTypeCoherence caught-indexed)
        source-function-no target-function-no function-related)
      (canonicalIndexedResults caught-indexed)
      transported-function-value vW vV′ transported-rank
