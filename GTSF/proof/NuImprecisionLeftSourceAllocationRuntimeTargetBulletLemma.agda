module
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletLemma
  where

-- File Charter:
--   * Supplies the canonical bullet-free left renaming dependency to the
--     source-allocation target-bullet proof.
--   * Exposes the direct target-bullet relation theorem.
--   * Contains no carrier, alias layer, postulate, hole, permissive option,
--     or termination bypass.

open import proof.NuImprecisionLeftRenameNoBulletProof using
  (left-rename-no-bullet)
open import
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletDef
  using (LeftSourceAllocationRuntimeTargetBulletᵀ)
open import
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletProof
  using (left-source-allocation-runtime-target-bullet-proofᵀ)


left-source-allocation-runtime-target-bulletᵀ :
  LeftSourceAllocationRuntimeTargetBulletᵀ
left-source-allocation-runtime-target-bulletᵀ =
  left-source-allocation-runtime-target-bullet-proofᵀ
    left-rename-no-bullet
