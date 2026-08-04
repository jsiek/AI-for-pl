module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootLemma
  where

-- File Charter:
--   * Exposes canonical ordinary target narrowing untag resumption.
--   * Supplies the completed target-tag cancellation theorem to the existing
--     strict root proof.
--   * Contains no additional theorem shape, result/view/outcome type,
--     postulate, hole, permissive option, or broad DGG import.

open import
  proof.Target.SealTag.NuImprecisionTargetTagCancellationLemma
  using (target-tag-cancellationᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootDef
  using (WorldCoherentRightTargetNarrowUntagRootᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetNarrowUntagRootProof
  using (right-target-narrow-untag-root-proofᵀ)


world-coherent-right-target-narrow-untag-rootᵀ :
  WorldCoherentRightTargetNarrowUntagRootᵀ
world-coherent-right-target-narrow-untag-rootᵀ =
  right-target-narrow-untag-root-proofᵀ target-tag-cancellationᵀ
