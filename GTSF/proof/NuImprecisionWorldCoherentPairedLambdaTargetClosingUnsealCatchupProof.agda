module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealCatchupProof
  where

-- File Charter:
--   * Proves the active unseal target-closing leaf impossible before any
--     source unseal or target-binder-closing operation is required.
--   * Uses canonical forms: a value of type `＇ zero` requires a seal-store
--     entry at `zero`, but a matched universal lift shifts every store name.
--   * Contains no intermediate pre-unseal relation, broad simulation import,
--     postulate, or permissive option.

open import Coercions using (cast-seal)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)
open import NuTermImprecision using
  ( leftStoreⁱ
  ; leftStoreⁱ-lift
  )
open import NuTerms using (⊢⟨⟩)
open import QuotientedTermImprecision using
  (nu-term-imprecision-source-typing)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import TermTyping using (forget)
open import Types using (⟰ᵗ)
open import
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealCatchupDef
  using (WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ)
open import proof.NuImprecisionWorldCoherenceProof using
  (zero-not-in-shifted-store)
open import proof.NuProgress using (canonical-＇; sv-seal)


world-coherent-paired-lambda-target-closing-unseal-catchup-proofᵀ :
  WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ
world-coherent-paired-lambda-target-closing-unseal-catchup-proofᵀ
    coherent exclusive wfL hA h⇑A unseal↑ liftν lift∀
    vW noW vW′ noW′ W⊑W′
    with canonical-＇ vW
      (forget (nu-term-imprecision-source-typing W⊑W′))
world-coherent-paired-lambda-target-closing-unseal-catchup-proofᵀ
    coherent exclusive wfL hA h⇑A unseal↑ liftν lift∀
    vW noW vW′ noW′ W⊑W′
    | sv-seal {A = Y} vV refl
    with forget (nu-term-imprecision-source-typing W⊑W′)
world-coherent-paired-lambda-target-closing-unseal-catchup-proofᵀ
    coherent exclusive wfL hA h⇑A unseal↑ liftν lift∀
    vW noW vW′ noW′ W⊑W′
    | sv-seal {A = Y} vV refl
    | ⊢⟨⟩ (cast-seal hY zeroY∈ ok) V⊢ =
  ⊥-elim
    (zero-not-in-shifted-store
      (subst ((zero , _) ∈_) (leftStoreⁱ-lift lift∀) zeroY∈))
