module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationProof
  where

-- File Charter:
--   * Proves exact active target-down synchronization inside QTIP by
--     exhaustive target-root dispatch.
--   * Delegates exactly the feasible identity, sequence, and untag roots to
--     smaller semantic cells.
--   * Eliminates instantiation and unseal roots by narrowing inversion and
--     eliminates target blame because the cast body is a value.
--   * Contains no frame recursion, postulate, hole, permissive option,
--     source-administration worker, or application case.

import NarrowWiden as NW
open import Data.Product using (_,_)
open import NuReduction using
  ( β-id
  ; β-inst
  ; β-seq
  ; blame-⟨⟩
  ; seal-unseal
  ; tag-untag-bad
  ; tag-untag-ok
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveRootsDef
  using
  ( WorldCoherentRightOneStepQuotientDownActiveRoots
  ; rightStepQuotientDownIdentityRoot
  ; rightStepQuotientDownSequenceRoot
  ; rightStepQuotientDownUntagRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownActiveSynchronizationDef
  using (WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ)


world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ :
  WorldCoherentRightOneStepQuotientDownActiveRoots →
  WorldCoherentRightOneStepQuotientDownActiveSynchronizationᵀ
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root@(β-id vBody) =
  rightStepQuotientDownIdentityRoot roots
    down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root@(β-seq vBody) =
  rightStepQuotientDownSequenceRoot roots
    down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape (d′⊢ , NW.cross ()) d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square (β-inst vBody)
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root@(tag-untag-ok vBody) =
  rightStepQuotientDownUntagRoot roots
    down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root@(tag-untag-bad vBody G≢H) =
  rightStepQuotientDownUntagRoot roots
    down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape d′⊒ d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square root
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′
    d⊒ d-shape (d′⊢ , NW.cross ()) d′-shape M⊑V′ down-square
    widening u-shape u′-shape up-square (seal-unseal vBody)
world-coherent-right-one-step-quotient-down-active-synchronization-proofᵀ
    roots down-mode coherent exclusive unique prefix wfL wfR
    ok-source ok-target () d⊒ d-shape d′⊒ d′-shape M⊑V′
    down-square widening u-shape u′-shape up-square blame-⟨⟩
