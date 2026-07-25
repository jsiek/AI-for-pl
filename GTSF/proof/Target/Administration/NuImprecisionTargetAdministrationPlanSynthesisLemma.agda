module proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisLemma where

-- File Charter:
--   * Exposes canonical target-administration plan synthesis.
--   * Threads exact cast shapes and imprecision-composition triangles into
--     hereditary plans, including strict sequence components.
--   * Distinguishes ordinary narrowing, ordinary widening, and identity-only
--     widening at the synthesis boundary.
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
