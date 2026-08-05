module InterpreterAdequacy.proof.PrimitiveTraceDecomposition where

-- File Charter:
--   * Decomposes a terminating primitive trace into operand phases and the
--     final primitive redex.
--   * Records the store-change action on the suspended operand and the
--     already evaluated left value.
--   * Uses only reduction determinism and value irreducibility.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

open import NuReduction
import NuTerms as N
open import Primitives using (Prim; addℕ)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.DGG.Core.NuReductionDeterminism using
  (blame-irreducible; value-irreducible)

record PrimitiveTraceDecomposition
    (L M : N.Term) (op : Prim) (changes : StoreChanges)
    (result : N.Term) : Set where
  constructor primitive-trace-decomposition
  field
    left-changes : StoreChanges
    right-changes : StoreChanges
    active-changes : StoreChanges
    left-value : N.Term
    right-value : N.Term
    left-is-value : N.Value left-value
    right-is-value : N.Value right-value
    left-trace : L —↠[ left-changes ] left-value
    right-trace :
      applyTerms left-changes M —↠[ right-changes ] right-value
    active-trace :
      (applyTerms right-changes left-value N.⊕[ op ] right-value)
        —↠[ active-changes ] result
    changes-eq :
      changes ≡ left-changes ++ (right-changes ++ active-changes)

open PrimitiveTraceDecomposition public

private
  value-trace-refl :
    ∀ {V changes U} →
    N.Value V →
    V —↠[ changes ] U →
    (changes ≡ []) × (U ≡ V)
  value-trace-refl vV ↠-refl = refl , refl
  value-trace-refl vV (↠-step V→L L↠U) =
    ⊥-elim (value-irreducible vV V→L)

  blame-does-not-reach-value :
    ∀ {changes V} →
    N.blame —↠[ changes ] V →
    N.Value V →
    ⊥
  blame-does-not-reach-value ↠-refl ()
  blame-does-not-reach-value (↠-step blame→L L↠V) vV =
    ⊥-elim (blame-irreducible blame→L)

  apply-term-value :
    ∀ change {V} → N.Value V → N.Value (applyTerm change V)
  apply-term-value keep vV = vV
  apply-term-value (bind A) vV = renameᵗᵐ-preserves-Value _ vV

prepend-left-step :
  ∀ {change changes L L′ M op result} →
  L —→[ change ] L′ →
  PrimitiveTraceDecomposition
    L′ (applyTerm change M) op changes result →
  PrimitiveTraceDecomposition L M op (change ∷ changes) result
prepend-left-step L→L′
    (primitive-trace-decomposition
      changes-L changes-M changes-A V U vV vU
      L′↠V M↠U active refl) =
  primitive-trace-decomposition
    (_ ∷ changes-L) changes-M changes-A V U vV vU
    (↠-step L→L′ L′↠V) M↠U active refl

prepend-right-step :
  ∀ {change changes L M M′ op result} →
  (vL : N.Value L) →
  M —→[ change ] M′ →
  PrimitiveTraceDecomposition
    (applyTerm change L) M′ op changes result →
  PrimitiveTraceDecomposition L M op (change ∷ changes) result
prepend-right-step {change = change} {L = L} vL M→M′
    (primitive-trace-decomposition
      changes-L changes-M changes-A V U vV vU
      shifted-L↠V M′↠U active changes-eq)
    with value-trace-refl (apply-term-value change vL) shifted-L↠V
prepend-right-step {change = change} {L = L} vL M→M′
    (primitive-trace-decomposition
      .[] changes-M changes-A .(applyTerm change L) U vV vU
      shifted-L↠V M′↠U active changes-eq)
    | refl , refl =
  primitive-trace-decomposition
    [] (change ∷ changes-M) changes-A L U vL vU
    ↠-refl (↠-step M→M′ M′↠U) active
    (cong (change ∷_) changes-eq)

decompose-primitive-value-trace :
  ∀ {L M op changes result} →
  (L N.⊕[ op ] M) —↠[ changes ] result →
  N.Value result →
  PrimitiveTraceDecomposition L M op changes result
decompose-primitive-value-trace ↠-refl ()
decompose-primitive-value-trace
    (↠-step (pure-step δ-⊕) tail) vR =
  primitive-trace-decomposition
    [] [] (keep ∷ _) (N.$ _) (N.$ _)
    (N.$ _) (N.$ _) ↠-refl ↠-refl
    (↠-step (pure-step δ-⊕) tail) refl
decompose-primitive-value-trace
    (↠-step (pure-step blame-⊕₁) tail) vR =
  ⊥-elim (blame-does-not-reach-value tail vR)
decompose-primitive-value-trace
    (↠-step (pure-step (blame-⊕₂ vV)) tail) vR =
  ⊥-elim (blame-does-not-reach-value tail vR)
decompose-primitive-value-trace
    (↠-step (ξ-⊕₁ L→L′ shift-M) tail) vR =
  prepend-left-step L→L′
    (decompose-primitive-value-trace tail vR)
decompose-primitive-value-trace
    (↠-step (ξ-⊕₂ vL shift-L M→M′) tail) vR =
  prepend-right-step vL M→M′
    (decompose-primitive-value-trace tail vR)
