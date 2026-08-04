module
  proof.Right.Target.NuImprecisionRightTargetWidenInstSourceOnlyLambdaRootProof
  where

-- File Charter:
--   * Proves the ordinary source-`Λ` leaf of source-only-final target
--     widening instantiation.
--   * Transports the target cast through the source-only store lift, frames
--     the body relation, and delegates universal closure to one capability.
--   * Contains no recursive dispatcher, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad simulation import.

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( rightStoreⁱ-lift-left
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import QuotientedTermImprecision using (⊑cast⊑ᵀ)
open import TermTyping using (SealModeStore★)
open import proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef using
  (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.Right.Target.NuImprecisionRightTargetWidenInstSourceOnlyLambdaRootDef
  using
  (WorldCoherentRightTargetWidenInstSourceOnlyLambdaRootᵀ)


world-coherent-right-target-widen-inst-source-only-lambda-root-proofᵀ :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetWidenInstSourceOnlyLambdaRootᵀ
world-coherent-right-target-widen-inst-source-only-lambda-root-proofᵀ
    source-all {q = q} prefix coherent exclusive unique wfR runtime
    vW noW mode seal★ c⊑ c-shape comp liftρ liftγ body =
  source-all prefix coherent exclusive unique wfR runtime
    vW noW liftρ liftγ
    (⊑cast⊑ᵀ mode lifted-seal lifted-cast body q c-shape comp)
  where
  lifted-seal =
    subst (SealModeStore★ _)
      (sym (rightStoreⁱ-lift-left liftρ)) seal★

  lifted-cast =
    subst
      (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      (sym (rightStoreⁱ-lift-left liftρ)) c⊑
