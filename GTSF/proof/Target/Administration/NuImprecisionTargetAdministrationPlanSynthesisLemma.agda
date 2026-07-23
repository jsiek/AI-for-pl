module proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisLemma where

-- File Charter:
--   * Exposes canonical target-administration plan synthesis.
--   * Confirms that existing narrowing/widening evidence supplies hereditary
--     sequence midpoints without changing QTI.
--   * Contains no simulation result, outcome carrier, compatibility alias,
--     postulate, hole, or permissive option.

open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef using
  (TargetAdministrationPlanSynthesis)
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisProof using
  (target-administration-plan-synthesis-proofᵀ)


target-administration-plan-synthesisᵀ :
  TargetAdministrationPlanSynthesis
target-administration-plan-synthesisᵀ =
  target-administration-plan-synthesis-proofᵀ
