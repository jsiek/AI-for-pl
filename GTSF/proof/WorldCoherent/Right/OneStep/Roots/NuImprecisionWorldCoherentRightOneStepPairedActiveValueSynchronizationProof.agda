module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationProof
  where

-- File Charter:
--   * Proves paired active-value synchronization by exhaustive target-root
--     dispatch.
--   * Delegates exactly the feasible identity, sequence, instantiation, and
--     unseal roots to smaller semantic cells.
--   * Eliminates target `tag-untag` roots by PairedCast inversion and target
--     blame because the target cast body is a value.
--   * Contains no recursive dispatcher, postulate, hole, permissive option,
--     source-administration worker, or quotient case.

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
  ( paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueRootsDef
  using
  ( WorldCoherentRightOneStepPairedActiveValueRoots
  ; rightStepPairedActiveValueIdentityRoot
  ; rightStepPairedActiveValueInstantiationRoot
  ; rightStepPairedActiveValueSequenceRoot
  ; rightStepPairedActiveValueUnsealRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepPairedActiveValueSynchronizationDef
  using (WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ)


world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ :
  WorldCoherentRightOneStepPairedActiveValueRoots →
  WorldCoherentRightOneStepPairedActiveValueSynchronizationᵀ
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root@(β-id vBody) =
  rightStepPairedActiveValueIdentityRoot roots
    coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root@(β-seq vBody) =
  rightStepPairedActiveValueSequenceRoot roots
    coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root@(β-inst vBody) =
  rightStepPairedActiveValueInstantiationRoot roots
    coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-conversion (paired-reveal corr source () replacement))
    V⊑V′ (tag-untag-ok vBody)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-conversion (paired-conceal corr source () replacement))
    V⊑V′ (tag-untag-ok vBody)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-widening mode seal★ c⊑ c-shape mode′ seal★′
      (c′⊢ , NW.cross ()) c′-shape source-comp target-comp compat)
    V⊑V′ (tag-untag-ok vBody)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-conversion (paired-reveal corr source () replacement))
    V⊑V′ (tag-untag-bad vBody G≢H)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-conversion (paired-conceal corr source () replacement))
    V⊑V′ (tag-untag-bad vBody G≢H)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    (paired-widening mode seal★ c⊑ c-shape mode′ seal★′
      (c′⊢ , NW.cross ()) c′-shape source-comp target-comp compat)
    V⊑V′ (tag-untag-bad vBody G≢H)
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root@(seal-unseal vBody) =
  rightStepPairedActiveValueUnsealRoot roots
    coherent exclusive unique wfL wfR
    ok-source ok-target vV noV vV′ noV′ noninert
    paired V⊑V′ root
world-coherent-right-one-step-paired-active-value-synchronization-proofᵀ
    roots coherent exclusive unique wfL wfR
    ok-source ok-target vV noV () noV′ noninert
    paired V⊑V′ blame-⟨⟩
