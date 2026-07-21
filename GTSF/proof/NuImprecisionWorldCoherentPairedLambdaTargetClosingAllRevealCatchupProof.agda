module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealCatchupProof
  where

-- File Charter:
--   * Packages the structural `reveal-all` target-closing relation as a
--     coherent terminal value catch-up.
--   * Consumes the remaining term-level paired-binder transformation through
--     its focused relation-level theorem boundary.
--   * Contains no semantic relation traversal, postulate, or permissive
--     option.

open import Data.List using (_∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( leftStoreⁱ
  ; leftStoreⁱ-lift-left
  )
open import NuTerms using
  ( Λ_
  ; no•-Λ
  ; no•-⟨⟩
  ; ok-no
  )
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Types using (⇑ᵗ)
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealRelationDef
  using (WorldCoherentPairedLambdaTargetClosingAllRevealRelationᵀ)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllRevealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingAllRevealCatchupᵀ)
open import proof.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.NuStoreProperties using (StoreWf-bind)


world-coherent-paired-lambda-target-closing-all-reveal-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingAllRevealRelationᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingAllRevealCatchupᵀ
world-coherent-paired-lambda-target-closing-all-reveal-catchup-proofᵀ
    close-relation value-catchup
    coherent exclusive wfL hA h⇑A inner
    liftν lift∀ vW noW vW′ noW′ W⊑W′ =
  value-catchup
    (world-coherent-left-allocation liftν coherent)
    (source-name-exclusive-source-only-head exclusive)
    allocated-wf
    (ok-no (no•-⟨⟩ noW))
    (Λ vW′)
    (no•-Λ noW′)
    (close-relation h⇑A inner liftν lift∀
      vW noW vW′ noW′ W⊑W′)
  where
  allocated-store-eq =
    cong ((zero , ⇑ᵗ _) ∷_) (leftStoreⁱ-lift-left liftν)

  allocated-wf =
    subst (StoreWf _) (sym allocated-store-eq) (StoreWf-bind wfL hA)
