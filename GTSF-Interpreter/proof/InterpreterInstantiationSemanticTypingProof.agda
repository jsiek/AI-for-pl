module proof.InterpreterInstantiationSemanticTypingProof where

-- File Charter:
--   * Implements unary semantic typing and error freedom for instantiation.
--   * Reuses the direct mutual interpreter typing induction.
--   * Contains no narrowing, small-step, or reduction-derived argument.

open import Relation.Binary.PropositionalEquality using (_≢_)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
open import proof.InterpreterErrorFreedomCore using
  (outcome-typing-excludes-error)
import proof.InterpreterTypingCore as Typing

instantiateValue-preserves-semantic-typing :
  ∀ n {W V body α} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W V (polymorphic-type body) →
  OutcomeTyping W
    (instantiateSemantic (nominal-type (seal-name α)) body)
    (instantiateValue W α V n)
instantiateValue-preserves-semantic-typing =
  Typing.instantiateValue-typing

instantiateValue-never-fails :
  ∀ n {W V body α U e} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W V (polymorphic-type body) →
  instantiateValue W α V n ≢ failed U e
instantiateValue-never-fails n W⊢ α-ok V⊢ =
  outcome-typing-excludes-error
    (instantiateValue-preserves-semantic-typing n W⊢ α-ok V⊢)
