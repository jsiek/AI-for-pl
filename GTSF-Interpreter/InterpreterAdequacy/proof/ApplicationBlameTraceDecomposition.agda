module InterpreterAdequacy.proof.ApplicationBlameTraceDecomposition where

-- File Charter:
--   * Decomposes an application trace ending in blame into the first phase
--     that blames: left operand, right operand, or active application.
--   * Records the exact store-change split, including the final propagation
--     step for an operand that blames.
--   * Uses only the official small-step relation and irreducibility facts.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import NuReduction
import NuTerms as N
import Coercions as C
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible; value-irreducible)

data ApplicationBlameTraceDecomposition
    (L M : N.Term) (changes : StoreChanges) : Set where
  left-blames :
    ∀ {changes-L} →
    L —↠[ changes-L ] N.blame →
    changes ≡ changes-L ++ (keep ∷ []) →
    ApplicationBlameTraceDecomposition L M changes

  right-blames :
    ∀ {changes-L changes-M f} →
    (vf : N.Value f) →
    L —↠[ changes-L ] f →
    applyTerms changes-L M —↠[ changes-M ] N.blame →
    changes ≡ changes-L ++ (changes-M ++ (keep ∷ [])) →
    ApplicationBlameTraceDecomposition L M changes

  active-blames :
    ∀ {changes-L changes-M changes-A f u} →
    (vf : N.Value f) →
    (vu : N.Value u) →
    L —↠[ changes-L ] f →
    applyTerms changes-L M —↠[ changes-M ] u →
    (applyTerms changes-M f N.· u) —↠[ changes-A ] N.blame →
    changes ≡ changes-L ++ (changes-M ++ changes-A) →
    ApplicationBlameTraceDecomposition L M changes

private
  blame-trace-refl :
    ∀ {changes} →
    N.blame —↠[ changes ] N.blame →
    changes ≡ []
  blame-trace-refl ↠-refl = refl
  blame-trace-refl (↠-step blame→L L↠blame) =
    ⊥-elim (blame-irreducible blame→L)

  value-does-not-reach-blame :
    ∀ {V changes} →
    N.Value V →
    V —↠[ changes ] N.blame →
    ⊥
  value-does-not-reach-blame () ↠-refl
  value-does-not-reach-blame vV (↠-step V→L L↠blame) =
    ⊥-elim (value-irreducible vV V→L)

  value-trace-refl :
    ∀ {V changes U} →
    N.Value V →
    V —↠[ changes ] U →
    (changes ≡ []) × (U ≡ V)
  value-trace-refl vV ↠-refl = refl , refl
  value-trace-refl vV (↠-step V→L L↠U) =
    ⊥-elim (value-irreducible vV V→L)

  apply-term-value :
    ∀ change {V} → N.Value V → N.Value (applyTerm change V)
  apply-term-value keep vV = vV
  apply-term-value (bind A) vV = renameᵗᵐ-preserves-Value _ vV

prepend-left-step :
  ∀ {change changes L L′ M} →
  L —→[ change ] L′ →
  ApplicationBlameTraceDecomposition
    L′ (applyTerm change M) changes →
  ApplicationBlameTraceDecomposition L M (change ∷ changes)
prepend-left-step L→L′ (left-blames L′↠blame refl) =
  left-blames (↠-step L→L′ L′↠blame) refl
prepend-left-step L→L′
    (right-blames vf L′↠f M↠blame refl) =
  right-blames vf (↠-step L→L′ L′↠f) M↠blame refl
prepend-left-step L→L′
    (active-blames vf vu L′↠f M↠u active refl) =
  active-blames vf vu (↠-step L→L′ L′↠f) M↠u active refl

prepend-right-step :
  ∀ {change changes L M M′} →
  (vL : N.Value L) →
  M —→[ change ] M′ →
  ApplicationBlameTraceDecomposition
    (applyTerm change L) M′ changes →
  ApplicationBlameTraceDecomposition L M (change ∷ changes)
prepend-right-step {change = change} vL M→M′
    (left-blames L↠blame changes-eq) =
  ⊥-elim
    (value-does-not-reach-blame
      (apply-term-value change vL) L↠blame)
prepend-right-step {change = change} {L = L} vL M→M′
    (right-blames vf shifted-L↠f M′↠blame changes-eq)
    with value-trace-refl (apply-term-value change vL) shifted-L↠f
prepend-right-step {change = change} {L = L} vL M→M′
    (right-blames vf shifted-L↠f M′↠blame changes-eq)
    | refl , refl =
  right-blames vL ↠-refl (↠-step M→M′ M′↠blame)
    (cong (change ∷_) changes-eq)
prepend-right-step {change = change} {L = L} vL M→M′
    (active-blames vf vu shifted-L↠f M′↠u active changes-eq)
    with value-trace-refl (apply-term-value change vL) shifted-L↠f
prepend-right-step {change = change} {L = L} vL M→M′
    (active-blames vf vu shifted-L↠f M′↠u active changes-eq)
    | refl , refl =
  active-blames vL vu ↠-refl (↠-step M→M′ M′↠u) active
    (cong (change ∷_) changes-eq)

decompose-application-blame-trace :
  ∀ {L M changes} →
  (L N.· M) —↠[ changes ] N.blame →
  ApplicationBlameTraceDecomposition L M changes
decompose-application-blame-trace
    (↠-step (pure-step (β vM)) tail) =
  active-blames (N.ƛ _) vM ↠-refl ↠-refl
    (↠-step (pure-step (β vM)) tail) refl
decompose-application-blame-trace
    (↠-step (pure-step
      (β-↦ {V = V} {W = W} {p = p} {q = q} vV vW)) tail) =
  active-blames (vV N.⟨ p C.↦ q ⟩) vW ↠-refl ↠-refl
    (↠-step (pure-step (β-↦ vV vW)) tail) refl
decompose-application-blame-trace
    (↠-step (pure-step blame-·₁) tail)
    with blame-trace-refl tail
decompose-application-blame-trace
    (↠-step (pure-step blame-·₁) tail) | refl =
  left-blames ↠-refl refl
decompose-application-blame-trace
    (↠-step (pure-step (blame-·₂ vV)) tail)
    with blame-trace-refl tail
decompose-application-blame-trace
    (↠-step (pure-step (blame-·₂ vV)) tail) | refl =
  right-blames vV ↠-refl ↠-refl refl
decompose-application-blame-trace
    (↠-step (ξ-·₁ L→L′ shiftM) tail) =
  prepend-left-step L→L′ (decompose-application-blame-trace tail)
decompose-application-blame-trace
    (↠-step (ξ-·₂ vL shiftL M→M′) tail) =
  prepend-right-step vL M→M′ (decompose-application-blame-trace tail)
