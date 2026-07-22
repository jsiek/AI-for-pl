module
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletProof
  where

-- File Charter:
--   * Proves the canonical target-runtime-bullet leaf for source-allocation
--     runtime transport.
--   * Delegates the bullet-free body renaming to `LeftRenameNoBullet` and
--     applies the existing target-bullet left-renaming theorem.
--   * Returns the renamed relation directly, without a path, result,
--     outcome, or view carrier.
--   * Contains no postulate, hole, permissive option, or termination bypass.

open import proof.NuImprecisionLeftRenameNoBulletDef using
  ( LeftRenameNoBullet
  ; left-rename-no•ᵀ
  )
open import
  proof.NuImprecisionLeftSourceAllocationRuntimeTargetBulletDef
  using (LeftSourceAllocationRuntimeTargetBulletᵀ)
open import proof.NuImprecisionSimulationCore using
  ( left-insertion-suc
  ; left-rename-⊑αᵀ
  )


left-source-allocation-runtime-target-bullet-proofᵀ :
  LeftRenameNoBullet →
  LeftSourceAllocationRuntimeTargetBulletᵀ
left-source-allocation-runtime-target-bullet-proofᵀ
    rename-no-bullet renameρ renameγ noN vL′ noL′ liftρ liftγ
    N⊑L′ L′•⊢ =
  left-rename-⊑αᵀ renameρ renameγ vL′ noL′ liftρ liftγ
    (λ renameρ′ renameγ′ →
      left-rename-no•ᵀ rename-no-bullet left-insertion-suc
        renameρ′ renameγ′ noN noL′ N⊑L′)
    L′•⊢
