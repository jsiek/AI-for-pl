module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingProof
  where

-- File Charter:
--   * Assembles the complete source-universal right-value closing theorem
--     from its flat semantic case capabilities.
--   * Composes the constructor-form value assembly with the exhaustive
--     source-value dispatcher.
--   * Contains no semantic case implementation, recursion, result/view type,
--     postulate, hole, permissive option, or broad simulation import.

open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  using (WorldCoherentRightSourceAllClosingCases)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingDispatcherProof
  using
  (world-coherent-right-source-all-closing-dispatcher-proofᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsProof
  using (world-coherent-right-source-all-value-forms-proof)
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)


world-coherent-right-source-all-closing-proofᵀ :
  WorldCoherentRightSourceAllClosingCases →
  WorldCoherentRightSourceAllClosingᵀ
world-coherent-right-source-all-closing-proofᵀ cases =
  world-coherent-right-source-all-closing-dispatcher-proofᵀ
    (world-coherent-right-source-all-value-forms-proof cases)
