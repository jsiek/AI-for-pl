module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsUnsealAssemblyAccDef
  where

-- File Charter:
--   * Defines closure of the accessibility-indexed pending-cast worker from
--     the sole remaining semantic instantiation/allocation residual.
--   * Keeps all recursive target-administration plans inside the ranked
--     worker so every back-edge consumes an explicit `Acc` predecessor.
--   * Contains no implementation, result/view/outcome carrier, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsAccDef
  using (WorldCoherentRightTargetPendingCastsAccᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingCastsInstResidualAccDef
  using (WorldCoherentRightTargetPendingCastsInstResidualAccᵀ)


WorldCoherentRightTargetPendingCastsUnsealAssemblyAccᵀ : Set₁
WorldCoherentRightTargetPendingCastsUnsealAssemblyAccᵀ =
  WorldCoherentRightTargetPendingCastsInstResidualAccᵀ →
  WorldCoherentRightTargetPendingCastsAccᵀ
