module proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupLemma where

-- File Charter:
--   * Assembles the source-universal lifted body catch-up from the canonical
--     ambient-prefix right-value dispatcher.
--   * Exposes the strict theorem while keeping callers independent of the
--     worker proof and case-record assembly.
--   * Contains no closing/collapse proof, postulate, hole, permissive option,
--     or compatibility wrapper.

open import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupDef using
  (WorldCoherentRightSourceAllBodyCatchupᵀ)
open import proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupProof using
  (world-coherent-right-source-all-body-catchup-proofᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupCasesDef using
  (WorldCoherentRightValueCatchupCases)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupDispatcherProof
  using (world-coherent-right-value-catchup-dispatcher-proofᵀ)


world-coherent-right-source-all-body-catchupᵀ :
  WorldCoherentRightValueCatchupCases →
  WorldCoherentRightSourceAllBodyCatchupᵀ
world-coherent-right-source-all-body-catchupᵀ cases =
  world-coherent-right-source-all-body-catchup-proofᵀ
    (world-coherent-right-value-catchup-dispatcher-proofᵀ cases)
