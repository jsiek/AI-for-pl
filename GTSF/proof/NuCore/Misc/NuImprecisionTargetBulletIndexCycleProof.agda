module proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleProof where

-- File Charter:
--   * Reduces the target-bullet index cycle to the common target-extension
--     obstruction.
--   * Right-lifts the pre-allocation index and pairs it with the supplied
--     post-allocation index at their common source endpoint.
--   * Contains no canonical dependency assembly, store, term relation,
--     simulation, postulate, hole, or permissive option.

open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  (⊑-target-lift-rightᵢ)
open import
  proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan
  using (pair-lower)
open import proof.NuCore.Misc.NuImprecisionCommonTargetExtensionCycleDef
  using (CommonTargetExtensionCycleᵀ)
open import proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleDef
  using (TargetBulletIndexCycleᵀ)


target-bullet-index-cycle-proofᵀ :
  CommonTargetExtensionCycleᵀ →
  TargetBulletIndexCycleᵀ
target-bullet-index-cycle-proofᵀ common q r =
  common (pair-lower r (⊑-target-lift-rightᵢ q))
