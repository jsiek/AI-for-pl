module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupProof
  where

-- File Charter:
--   * Packages structural universal widening after paired target-binder
--     closing as a coherent terminal value catch-up.
--   * Delegates only the reusable relation transport and the canonical
--     already-terminal coherent catch-up operations.
--   * Contains no relation traversal, broad simulation import, postulate, or
--     permissive option.

import Coercions as C
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
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using (cast⊑⊑ᵀ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import TermTyping using (cast-inst)
open import Types using (★; wf★)
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.NuImprecisionPairedLambdaTargetClosingRelationDef using
  (PairedLambdaTargetClosingRelationᵀ)
open import proof.NuImprecisionWorldCoherenceLemma using
  (world-coherent-left-allocation)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ)
open import proof.NuImprecisionWorldCoherentValueCatchupDef using
  (WorldCoherentLeftValueCatchupᵀ)
open import proof.NuStoreProperties using (StoreWf-bind)


world-coherent-paired-lambda-target-closing-all-widen-catchup-proofᵀ :
  PairedLambdaTargetClosingRelationᵀ →
  WorldCoherentLeftValueCatchupᵀ →
  WorldCoherentPairedLambdaTargetClosingAllWidenCatchupᵀ
world-coherent-paired-lambda-target-closing-all-widen-catchup-proofᵀ
    close-relation value-catchup {p = p}
    coherent exclusive wfL mode seal★ c⊑
    liftν lift∀ vW noW vW′ noW′ W⊑W′
    with close-relation liftν lift∀ vW noW vW′ noW′ W⊑W′
world-coherent-paired-lambda-target-closing-all-widen-catchup-proofᵀ
    close-relation value-catchup {p = p}
    coherent exclusive wfL mode seal★ c⊑
    liftν lift∀ vW noW vW′ noW′ W⊑W′
    | q , W⊑ΛW′ =
  value-catchup
    (world-coherent-left-allocation liftν coherent)
    (source-name-exclusive-source-only-head exclusive)
    allocated-wf
    (ok-no (no•-⟨⟩ noW))
    (Λ vW′)
    (no•-Λ noW′)
    (cast⊑⊑ᵀ (cast-inst mode) seal★ c⊑ W⊑ΛW′
      (⊑-source-liftνᵢ p))
  where
  allocated-store-eq =
    cong ((zero , ★) ∷_) (leftStoreⁱ-lift-left liftν)

  allocated-wf =
    subst (StoreWf _) (sym allocated-store-eq) (StoreWf-bind wfL wf★)
