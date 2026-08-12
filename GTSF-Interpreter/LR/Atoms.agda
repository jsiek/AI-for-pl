module LR.Atoms where

-- File Charter:
--   * Defines the small step-indexed relations used as atomic leaves of the
--     interpreter logical relation.
--   * Records downward closure explicitly and packages the semantic types on
--     the two sides of an atom.
--   * Contains no Kripke-world or structural logical-relation definition.

open import Data.Nat using (ℕ; suc)

open import Interpreter using (Value; World)
open import Typing.InterpreterSemanticTypingCore using
  (SemanticType; ValueTyping)

StepIndexedRelation : Set₁
StepIndexedRelation = ℕ → Value → Value → Set

DownwardClosed : StepIndexedRelation → Set
DownwardClosed R =
  ∀ {n : ℕ} {V V′ : Value}
  → R (suc n) V V′
  → R n V V′

record Atom : Set₁ where
  constructor atom
  field
    left-type : SemanticType
    right-type : SemanticType
    relation : StepIndexedRelation
    relation-downward : DownwardClosed relation

open Atom public

record AtomHolds (a : Atom) (n : ℕ) (V V′ : Value) : Set where
  constructor atom-holds
  field
    relation-holds : relation a n V V′

open AtomHolds public

record TypedAtom
    (W W′ : World) (a : Atom) (n : ℕ) (V V′ : Value) : Set₁ where
  constructor typed-atom
  field
    left-value-typed : ValueTyping W V (left-type a)
    right-value-typed : ValueTyping W′ V′ (right-type a)
    atom-related : AtomHolds a n V V′

open TypedAtom public
