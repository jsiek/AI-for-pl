module
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceWidenFrameContextProof
  where

-- File Charter:
--   * Proves that source widening framing preserves the contextual catch-up
--     equation and target-only store lineage.
--   * Reuses the canonical source-frame proof after exposing its two
--     source-silence equalities.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (right-value-indexed-catchup)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (world-coherent-right-value-indexed-catchup)
open import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesDef
  using (rightSourceWidenFrame)
open import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceFramesLemma
  using (world-coherent-right-source-frames)
open import
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceWidenFrameContextDef
  using (WorldCoherentRightSourceWidenFrameContextᵀ)


world-coherent-right-source-widen-frame-context-proofᵀ :
  WorldCoherentRightSourceWidenFrameContextᵀ
world-coherent-right-source-widen-frame-context-proofᵀ
    prefix coherent exclusive unique wfR okM′ vM noM inert
    mode seal★ c⊑ M⊑M′
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix =
  rightSourceWidenFrame world-coherent-right-source-frames
      prefix coherent exclusive unique wfR okM′ vM noM inert
      mode seal★ c⊑ M⊑M′ inner ,
  context-eq ,
  right-prefix
