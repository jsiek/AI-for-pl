module
  proof.NuImprecisionWorldCoherentRightSourceRevealFrameContextProof
  where

-- File Charter:
--   * Proves that source reveal framing preserves the contextual catch-up
--     equation and target-only store lineage.
--   * Reuses the canonical source-frame proof after exposing its two
--     source-silence equalities.
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
  using (rightSourceRevealFrame)
open import
  proof.NuImprecisionWorldCoherentRightSourceFramesLemma
  using (world-coherent-right-source-frames)
open import
  proof.NuImprecisionWorldCoherentRightSourceRevealFrameContextDef
  using (WorldCoherentRightSourceRevealFrameContextᵀ)


world-coherent-right-source-reveal-frame-context-proofᵀ :
  WorldCoherentRightSourceRevealFrameContextᵀ
world-coherent-right-source-reveal-frame-context-proofᵀ
    prefix coherent exclusive unique wfR okM′ vM noM inert
    c↑ M⊑M′
    inner@(world-coherent-right-value-indexed-catchup
      (right-value-indexed-catchup
        indexed refl refl source-value source-no-bullet
        target-value target-no-bullet transport type-coherence)
      lineage bullet final-world
      final-exclusive final-unique final-wfR)
    context-eq right-prefix =
  rightSourceRevealFrame world-coherent-right-source-frames
      prefix coherent exclusive unique wfR okM′ vM noM inert
      c↑ M⊑M′ inner ,
  context-eq ,
  right-prefix
