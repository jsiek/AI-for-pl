module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootProof
  where

-- File Charter:
--   * Assembles the three exact live paired source-active value-root cases.
--   * Keeps reveal, conceal, and widening proof bodies in focused modules so
--     each semantic case can be checked independently.
--   * Contains no transport implementation, retired `PairedCast` abstraction,
--     quotient case, recursive dispatcher, postulate, hole, or option.

open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveConcealValueRootProof
  using (active-paired-conceal-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveRevealValueRootProof
  using (active-paired-reveal-root-proofᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveValueRootDef
  using (WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedSourceActiveWideningValueRootProof
  using (active-paired-widening-root-proofᵀ)
open import
  proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupDef
  using (WorldCoherentLeftValueCatchupᵀ)


world-coherent-right-one-step-paired-source-active-value-root-proofᵀ :
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ →
  WorldCoherentRightOneStepPairedSourceActiveValueRootᵀ
world-coherent-right-one-step-paired-source-active-value-root-proofᵀ
    catchup synchronize =
  record
    { active-paired-reveal-root =
        active-paired-reveal-root-proofᵀ catchup synchronize
    ; active-paired-conceal-root =
        active-paired-conceal-root-proofᵀ catchup synchronize
    ; active-paired-widening-root =
        active-paired-widening-root-proofᵀ catchup synchronize
    }
