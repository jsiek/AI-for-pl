module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionProof
  where

-- File Charter:
--   * Proves the paired-final target-instantiation body inversion by
--     exhaustive typed `InstSafe` constructor analysis.
--   * Returns an inert all coercion or the exact active nested-instantiation
--     residual, while recording that the source body is universal.
--   * Contains no recursive dispatcher, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, catch-all, or broad DGG
--     import.

open import Agda.Builtin.Equality using (refl)
import Coercions as C
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import NarrowWiden as NW
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionDef
  using
  (WorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionᵀ)


world-coherent-right-target-pending-nu-allocation-paired-final-body-inversion-proofᵀ :
  WorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionᵀ
world-coherent-right-target-pending-nu-allocation-paired-final-body-inversion-proofᵀ
    (C.cast-inst hE occ (C.cast-all t⊢) ,
     NW.inst (NW.safe-all tʷ)) =
  _ , refl , inj₁ (C.`∀ _)
world-coherent-right-target-pending-nu-allocation-paired-final-body-inversion-proofᵀ
    (C.cast-inst hE occ
      (C.cast-inst hB occB t⊢) ,
     NW.inst (NW.safe-inst safe)) =
  _ , refl , inj₂ (_ , _ , refl , safe)
