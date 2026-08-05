module Runtime.InterpreterPolymorphicValueCanonical where

-- File Charter:
--   * States the semantic canonical-forms theorem for polymorphic values.
--   * Exposes exactly the three runtime constructors accepted by
--     `instantiateValue`.
--   * Delegates the exhaustive typing inversion to a focused proof module.

open import Interpreter using (Value)
open import Runtime.InterpreterPolymorphicValueCanonicalCore public
open import Typing.InterpreterSemanticTypingCore using
  (SemanticType; ValueTyping; polymorphic-type)
import proof.InterpreterPolymorphicValueCanonicalProof as Proof

polymorphic-value-canonical :
  ∀ {W V body} →
  ValueTyping W V (polymorphic-type body) →
  PolymorphicValueShape V
polymorphic-value-canonical =
  Proof.polymorphic-value-canonical
