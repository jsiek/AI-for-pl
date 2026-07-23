module
  proof.NuImprecisionWorldCoherentRightSourceNarrowFrameContextProof
  where

-- File Charter:
--   * Proves that source narrowing framing preserves the contextual catch-up
--     equation and target-only store lineage.
--   * Reuses the canonical source-frame proof, whose final world and target
--     trace are definitionally unchanged.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import proof.NuImprecisionRightValueCatchupResultDef using
  (right-value-indexed-catchup)
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using (world-coherent-right-value-indexed-catchup)
open import
  proof.NuImprecisionWorldCoherentRightSourceFramesDef
  using (rightSourceNarrowFrame)
open import
  proof.NuImprecisionWorldCoherentRightSourceFramesLemma
  using (world-coherent-right-source-frames)
open import
  proof.NuImprecisionWorldCoherentRightSourceNarrowFrameContextDef
  using (WorldCoherentRightSourceNarrowFrameContextᵀ)


world-coherent-right-source-narrow-frame-context-proofᵀ :
  WorldCoherentRightSourceNarrowFrameContextᵀ
world-coherent-right-source-narrow-frame-context-proofᵀ
    prefix coherent exclusive unique wfR okM′ vM noM inert
    mode seal★ c⊒ M⊑M′
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix =
  rightSourceNarrowFrame world-coherent-right-source-frames
      prefix coherent exclusive unique wfR okM′ vM noM inert
      mode seal★ c⊒ M⊑M′ inner ,
  context-eq ,
  right-prefix
