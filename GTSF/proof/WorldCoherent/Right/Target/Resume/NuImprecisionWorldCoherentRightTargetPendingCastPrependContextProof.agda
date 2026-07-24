module
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextProof
  where

-- File Charter:
--   * Proves contextual target-step prepending beneath an arbitrary pending
--     cast list.
--   * Lifts the step through every target cast and delegates only the final
--     context-preserving prepend operation.
--   * Contains no result/view/outcome type, postulate, hole, permissive
--     option, termination bypass, compatibility shim, or broad DGG import.

open import Coercions using (Coercion)
open import Data.List using (List; []; _∷_)
open import NuReduction using (keep; ξ-⟨⟩; _—→[_]_)
open import NuTerms using (Term)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)
open import
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetKeepPrependContextDef
  using (WorldCoherentRightTargetKeepPrependContextᵀ)
open import
  proof.WorldCoherent.Right.Target.Resume.NuImprecisionWorldCoherentRightTargetPendingCastPrependContextDef
  using (WorldCoherentRightTargetPendingCastPrependContextᵀ)


private
  lift-target-step-through-pending :
    ∀ (cs : List Coercion) {M′ N′ : Term} →
    M′ —→[ keep ] N′ →
    applyTargetPendingCasts M′ cs —→[ keep ]
      applyTargetPendingCasts N′ cs
  lift-target-step-through-pending [] target→ = target→
  lift-target-step-through-pending (c ∷ cs) target→ =
    lift-target-step-through-pending cs (ξ-⟨⟩ target→)


world-coherent-right-target-pending-cast-prepend-context-proofᵀ :
  WorldCoherentRightTargetKeepPrependContextᵀ →
  WorldCoherentRightTargetPendingCastPrependContextᵀ
world-coherent-right-target-pending-cast-prepend-context-proofᵀ
    prepend {cs = cs} target→ caught context-eq right-prefix =
  prepend
    (lift-target-step-through-pending cs target→)
    caught context-eq right-prefix
