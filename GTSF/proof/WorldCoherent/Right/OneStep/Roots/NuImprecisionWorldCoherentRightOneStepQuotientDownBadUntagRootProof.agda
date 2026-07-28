module
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootProof
  where

-- File Charter:
--   * Proves the failed target tag/untag root adapter from the exact
--     paired-down source-blame synchronization contract.
--   * Lifts the source-downcast trace through the closing source widening and
--     removes the resulting cast around blame.
--   * Contains no paired-down source-form analysis, quotient elimination,
--     recursive worker, postulate, hole, permissive option, compatibility
--     alias, or termination bypass.

open import Coercions using (Coercion)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_,_)
open import NuReduction using
  (blame-⟨⟩; keep; pure-step; ↠-refl; ↠-step)
open import NuTerms using
  (RuntimeOK; Term; no•-⟨⟩; ok-no; ok-⟨⟩; _⟨_⟩)
open import proof.Core.Properties.ReductionProperties using
  (cast-↠; ↠-trans)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentQuotientDownBadUntagSourceBlameDef
  using (WorldCoherentQuotientDownBadUntagSourceBlameᵀ)
open import
  proof.WorldCoherent.Right.OneStep.Roots.NuImprecisionWorldCoherentRightOneStepQuotientDownBadUntagRootDef
  using (WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ)


private
  runtime-cast⁻¹ :
    ∀ {M : Term} {c : Coercion} →
    RuntimeOK (M ⟨ c ⟩) →
    RuntimeOK M
  runtime-cast⁻¹ (ok-no (no•-⟨⟩ noM)) = ok-no noM
  runtime-cast⁻¹ (ok-⟨⟩ okM) = okM


world-coherent-right-one-step-quotient-down-bad-untag-root-proofᵀ :
  WorldCoherentQuotientDownBadUntagSourceBlameᵀ →
  WorldCoherentRightOneStepQuotientDownBadUntagRootᵀ
world-coherent-right-one-step-quotient-down-bad-untag-root-proofᵀ
    source-blame
    down-mode vV noV vW noW coherent exclusive unique wfL wfR
    ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape relation down-square elimination
    widening u-shape u′-shape up-square compatible root
    with source-blame
      down-mode vV noV vW noW coherent exclusive unique wfL wfR
      (runtime-cast⁻¹ ok-source) (runtime-cast⁻¹ ok-target)
      d⊒ d-shape d′⊒ d′-shape relation down-square elimination root
world-coherent-right-one-step-quotient-down-bad-untag-root-proofᵀ
    source-blame
    down-mode vV noV vW noW coherent exclusive unique wfL wfR
    ok-source ok-target
    d⊒ d-shape d′⊒ d′-shape relation down-square elimination
    widening u-shape u′-shape up-square compatible root
    | χs , source-trace =
  χs ++ keep ∷ [] ,
  ↠-trans (cast-↠ source-trace)
    (↠-step (pure-step blame-⟨⟩) ↠-refl)
