module Typing.InterpreterInstantiationSemanticTyping where

-- File Charter:
--   * Public unary semantic typing and error freedom for `instantiateValue`.
--   * States the result type by direct semantic instantiation.
--   * Delegates the mutual fuel proof to a reduction-free private module.

open import Relation.Binary.PropositionalEquality using (_≢_)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
import proof.InterpreterInstantiationSemanticTypingProof as Proof

instantiateValue-preserves-semantic-typing :
  ∀ n {W V body α} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W V (polymorphic-type body) →
  OutcomeTyping W
    (instantiateSemantic (nominal-type (seal-name α)) body)
    (instantiateValue W α V n)
instantiateValue-preserves-semantic-typing =
  Proof.instantiateValue-preserves-semantic-typing

instantiateValue-never-fails :
  ∀ n {W V body α U e} →
  WorldTyping W →
  Allocated W α →
  ValueTyping W V (polymorphic-type body) →
  instantiateValue W α V n ≢ failed U e
instantiateValue-never-fails =
  Proof.instantiateValue-never-fails
