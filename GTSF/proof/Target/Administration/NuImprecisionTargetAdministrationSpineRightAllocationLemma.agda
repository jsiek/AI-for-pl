module
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationLemma
  where

-- File Charter:
--   * Exposes the canonical hereditary target-administration spine transport
--     through one right-only runtime allocation.
--   * Supplies the completed structural proof without introducing an alias,
--     compatibility layer, postulate, hole, or permissive option.

open import
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationDef
  using (TargetAdministrationSpineRightAllocationᵀ)
open import
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationProof
  using (target-administration-spine-right-allocation-proofᵀ)


target-administration-spine-right-allocationᵀ :
  TargetAdministrationSpineRightAllocationᵀ
target-administration-spine-right-allocationᵀ =
  target-administration-spine-right-allocation-proofᵀ
