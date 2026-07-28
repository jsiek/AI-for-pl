module
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstSourceOnlyLambdaRootContextProof
  where

-- File Charter:
--   * Proves the contextual pre-`β-inst` source-`Λ` leaf for a source-only
--     final universal precision index.
--   * Transports the target cast through the source-only store lift, frames
--     the body relation, and delegates contextual universal closing.
--   * Contains no recursive dispatcher, result/view/outcome type, postulate,
--     hole, permissive option, termination bypass, or broad DGG import.

open import Relation.Binary.PropositionalEquality using (subst; sym)

open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( rightStoreⁱ-lift-left
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import QuotientedTermImprecision using (⊑cast⊑ᵀ)
open import TermTyping using (SealModeStore★)
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingContextDef
  using (WorldCoherentRightSourceAllClosingContextᵀ)
open import
  proof.WorldCoherent.Right.Target.WidenNarrow.NuImprecisionWorldCoherentRightTargetWidenInstSourceOnlyLambdaRootContextDef
  using (WorldCoherentRightTargetWidenInstSourceOnlyLambdaRootContextᵀ)


world-coherent-right-target-widen-inst-source-only-lambda-root-context-proofᵀ :
  WorldCoherentRightSourceAllClosingContextᵀ →
  WorldCoherentRightTargetWidenInstSourceOnlyLambdaRootContextᵀ
world-coherent-right-target-widen-inst-source-only-lambda-root-context-proofᵀ
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
