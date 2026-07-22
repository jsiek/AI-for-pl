module
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCasesProof
  where

-- File Charter:
--   * Assembles representative-inst path semantics from the identity,
--     leading-source-step, and leading-target-step contracts.
--   * Makes the complete top-level path split strict before any semantic case
--     implementation exists.

open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathCatchupDef
  using
  ( WorldCoherentQuotientRepresentativeInstPathCatchupᵀ
  ; path-refl
  ; path-step
  )
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathIdentityCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathSourceStepCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ)
open import
  proof.NuImprecisionWorldCoherentQuotientRepresentativeInstPathTargetStepCatchupDef
  using (WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ)


world-coherent-quotient-representative-inst-path-cases-proofᵀ :
  WorldCoherentQuotientRepresentativeInstPathIdentityCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathSourceStepCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathTargetStepCatchupᵀ →
  WorldCoherentQuotientRepresentativeInstPathCatchupᵀ
world-coherent-quotient-representative-inst-path-cases-proofᵀ
    identity source-step target-step
    path-refl path-refl
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  identity coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
world-coherent-quotient-representative-inst-path-cases-proofᵀ
    identity source-step target-step
    path-refl (path-step step rest)
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  target-step {step = step} {rest = rest}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
world-coherent-quotient-representative-inst-path-cases-proofᵀ
    identity source-step target-step
    (path-step step rest) targetPath
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening =
  source-step {step = step} {rest = rest} {targetPath = targetPath}
    coherent exclusive wfL okN vVd noVd vV′ noV′
    inert-d′ inert-u′ down widening
