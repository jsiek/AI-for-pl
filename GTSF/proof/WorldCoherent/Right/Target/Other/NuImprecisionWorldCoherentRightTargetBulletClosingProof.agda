module
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingProof
  where

-- File Charter:
--   * Proves target runtime-bullet closing from the type-only index cycle.
--   * Uses both precision indices retained by `⊑αᵀ`; right-lifting the
--     first and pairing it with the second gives the forbidden common-target
--     extension.
--   * Contains no target administration, recursive worker, result/view/
--     outcome type, postulate, hole, permissive option, compatibility
--     wrapper, or broad simulation import.

open import Data.Empty using (⊥-elim)
open import
  proof.NuCore.Misc.NuImprecisionTargetBulletIndexCycleDef
  using (TargetBulletIndexCycleᵀ)
open import
  proof.WorldCoherent.Right.Target.Other.NuImprecisionWorldCoherentRightTargetBulletClosingDef
  using (WorldCoherentRightTargetBulletClosingᵀ)


world-coherent-right-target-bullet-closing-proofᵀ :
  TargetBulletIndexCycleᵀ →
  WorldCoherentRightTargetBulletClosingᵀ
world-coherent-right-target-bullet-closing-proofᵀ
    cycle {q = q} {r = r}
    h⇑A prefix coherent exclusive unique wfR runtime
    vN noN vL′ noL′ liftρ liftγ relation
    source-typing target-typing =
  ⊥-elim (cycle q r)
