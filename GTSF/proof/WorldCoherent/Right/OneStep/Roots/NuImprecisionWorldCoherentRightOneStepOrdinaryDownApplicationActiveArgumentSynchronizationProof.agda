module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationProof
  where

-- File Charter:
--   * Implements active target narrowing dispatch in the argument of
--     `ordinary-down-applicationᵖᵀ`.
--   * Delegates exactly the feasible identity, sequence, and untag roots to
--     their full-context semantic cells.
--   * Eliminates instantiation and unseal roots by narrowing inversion and
--     eliminates target blame because the cast body is a value.
--   * Contains no QTIP-to-QTI conversion, recursion, postulate, hole,
--     permissive option, catch-all, or cast-mode restriction.

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
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRootsDef
  using
  ( WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRoots
  ; rightStepOrdinaryDownApplicationIdentityArgumentRoot
  ; rightStepOrdinaryDownApplicationSequenceArgumentRoot
  ; rightStepOrdinaryDownApplicationUntagArgumentRoot
  )
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationDef
  using
  (WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationᵀ)


world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ :
  WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentRoots →
  WorldCoherentRightOneStepOrdinaryDownApplicationActiveArgumentSynchronizationᵀ
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root@(β-id vV′) =
  rightStepOrdinaryDownApplicationIdentityArgumentRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root@(β-seq vV′) =
  rightStepOrdinaryDownApplicationSequenceArgumentRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′
    (d′⊢ , NW.cross ()) d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ (β-inst vV′)
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root@(tag-untag-ok vV′) =
  rightStepOrdinaryDownApplicationUntagArgumentRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root@(tag-untag-bad vV′ G≢H) =
  rightStepOrdinaryDownApplicationUntagArgumentRoot roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ root
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′
    (d′⊢ , NW.cross ()) d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ vM′ (seal-unseal vV′)
world-coherent-right-one-step-ordinary-down-application-active-argument-synchronization-proofᵀ
    roots
    coherent exclusive unique prefix wfL wfR
    ok-source ok-target source-typing target-typing
    mode seal★ d⊒ d-shape mode′ seal★′ d′⊒ d′-shape
    L⊑L′ M⊑M′ down-square
    widening u-shape u′-shape up-square
    vL′ () blame-⟨⟩
