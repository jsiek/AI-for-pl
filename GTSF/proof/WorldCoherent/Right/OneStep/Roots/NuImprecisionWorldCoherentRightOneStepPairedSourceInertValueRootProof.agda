module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootProof
  where

-- File Charter:
--   * Assembles the three exact live paired source-inert value-root cases.
--   * Keeps reveal, conceal, and widening proof bodies in focused modules so
--     each semantic case can be checked independently.
--   * Contains no transport implementation, retired `PairedCast` abstraction,
--     quotient case, recursive dispatcher, postulate, hole, or option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertConcealValueRootProof
  using (inert-paired-conceal-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertRevealValueRootProof
  using (inert-paired-reveal-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertValueRootDef
  using (WorldCoherentRightOneStepPairedSourceInertValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceInertWideningValueRootProof
  using (inert-paired-widening-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepValueIndexedRootDef
  using (WorldCoherentRightOneStepValueIndexedRootᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-source-inert-value-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepValueIndexedRootᵀ →
  WorldCoherentRightOneStepPairedSourceInertValueRootᵀ
world-coherent-right-one-step-paired-source-inert-value-root-proofᵀ
    catchup value-root =
  record
    { inert-paired-reveal-root =
        inert-paired-reveal-root-proofᵀ catchup value-root
    ; inert-paired-conceal-root =
        inert-paired-conceal-root-proofᵀ catchup value-root
    ; inert-paired-widening-root =
        inert-paired-widening-root-proofᵀ catchup value-root
    }
