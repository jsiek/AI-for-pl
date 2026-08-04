module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextLemma
  where

-- File Charter:
--   * Exposes the canonical contextual inert target-framing theorem.
--   * Separates the stable theorem name from its proof implementation.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextDef
  using (WorldCoherentRightTargetInertFramingContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetInertFramingContextProof
  using
  (world-coherent-right-target-inert-framing-context-proofᵀ)


world-coherent-right-target-inert-framing-contextᵀ :
  WorldCoherentRightTargetInertFramingContextᵀ
world-coherent-right-target-inert-framing-contextᵀ =
  world-coherent-right-target-inert-framing-context-proofᵀ
