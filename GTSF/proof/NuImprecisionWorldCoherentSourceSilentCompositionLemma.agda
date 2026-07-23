module
  proof.NuImprecisionWorldCoherentSourceSilentCompositionLemma
  where

-- File Charter:
--   * Exposes canonical world-coherent source-silent composition.
--   * Keeps the frozen statement, structural proof, and assembly separate.
--   * Contains no postulate, hole, or permissive option.

open import proof.NuImprecisionSourceSilentCompositionLemma using
  (source-silent-compositionᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionDef
  using (WorldCoherentSourceSilentCompositionᵀ)
open import
  proof.NuImprecisionWorldCoherentSourceSilentCompositionProof
  using (world-coherent-source-silent-composition-proofᵀ)


world-coherent-source-silent-compositionᵀ :
  WorldCoherentSourceSilentCompositionᵀ
world-coherent-source-silent-compositionᵀ =
  world-coherent-source-silent-composition-proofᵀ
    source-silent-compositionᵀ
