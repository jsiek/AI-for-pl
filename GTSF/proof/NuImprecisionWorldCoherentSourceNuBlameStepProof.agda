module proof.NuImprecisionWorldCoherentSourceNuBlameStepProof where

-- File Charter:
--   * Proves the world-coherent source `ν`-blame step case.
--   * Adapts the canonical source keep-step blame-root lemma using the exact
--     `ν`-blame keep step from `NuReduction`.
--   * Contains no dispatcher, postulate, hole, incomplete match, or
--     permissive option.

open import NuReduction using (blame-ν)
open import proof.NuImprecisionSourceOneStepBlameRootLemma using
  (world-coherent-source-keep-blame-rootᵀ)
open import proof.NuImprecisionWorldCoherentSourceNuBlameStepDef using
  (WorldCoherentSourceNuBlameStepᵀ)


world-coherent-source-ν-blame-step-proofᵀ :
  WorldCoherentSourceNuBlameStepᵀ
world-coherent-source-ν-blame-step-proofᵀ
    prefix coherent exclusive wfL wfR okνblame okM′
    νblame⊢ M′⊢ νblame⊑M′ =
  world-coherent-source-keep-blame-rootᵀ
    prefix coherent exclusive wfL wfR okνblame okM′
    νblame⊢ M′⊢ νblame⊑M′ blame-ν
