module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationProof
  where

-- File Charter:
--   * Proves quotient active-value synchronization by exhaustive target-root
--     dispatch.
--   * Delegates exactly the feasible identity, sequence, instantiation, and
--     unseal roots to smaller semantic cells.
--   * Eliminates target `tag-untag` roots by quotient-widening inversion and
--     target blame because the target cast body is a value.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     source-administration worker, ordinary paired-cast proof, or QTIP
--     recursion.

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
open import QuotientedTermImprecision using
  ( quotient-cast-widening
  ; quotient-id-widening
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueRootsDef
  using
  ( WorldCoherentRightOneStepQuotientActiveValueRoots
  ; rightStepQuotientActiveValueIdentityRoot
  ; rightStepQuotientActiveValueInstantiationRoot
  ; rightStepQuotientActiveValueSequenceRoot
  ; rightStepQuotientActiveValueUnsealRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ)


world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ :
  WorldCoherentRightOneStepQuotientActiveValueRoots →
  WorldCoherentRightOneStepQuotientActiveValueSynchronizationᵀ
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root@(β-id vBody) =
  rightStepQuotientActiveValueIdentityRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root@(β-seq vBody) =
  rightStepQuotientActiveValueSequenceRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root@(β-inst vBody) =
  rightStepQuotientActiveValueInstantiationRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′
    (quotient-id-widening u⊑ (u′⊢ , NW.cross ()))
    u-shape u′-shape up-square (tag-untag-ok vBody)
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′
      (u′⊢ , NW.cross ()))
    u-shape u′-shape up-square (tag-untag-ok vBody)
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′
    (quotient-id-widening u⊑ (u′⊢ , NW.cross ()))
    u-shape u′-shape up-square (tag-untag-bad vBody G≢H)
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′
    (quotient-cast-widening mode seal★ u⊑ mode′ seal★′
      (u′⊢ , NW.cross ()))
    u-shape u′-shape up-square (tag-untag-bad vBody G≢H)
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root@(seal-unseal vBody) =
  rightStepQuotientActiveValueUnsealRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target vV′ N⊑V′ widening u-shape u′-shape
    up-square root
world-coherent-right-one-step-quotient-active-value-synchronization-proofᵀ
    roots coherent exclusive unique prefix wfL wfR
    ok-source ok-target () N⊑V′ widening u-shape u′-shape
    up-square blame-⟨⟩
