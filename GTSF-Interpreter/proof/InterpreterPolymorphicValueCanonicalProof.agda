module proof.InterpreterPolymorphicValueCanonicalProof where

-- File Charter:
--   * Proves semantic canonical forms for polymorphic interpreter values.
--   * Inverts only the unary semantic value-typing derivation.
--   * Contains no interpreter execution, reduction, or narrowing theorem.

open import Interpreter using (Value)
open import Runtime.InterpreterPolymorphicValueCanonicalCore
  using (PolymorphicValueShape)
open PolymorphicValueShape
open import Typing.InterpreterSemanticTypingCore

polymorphic-value-canonical :
  ∀ {W V body} →
  ValueTyping W V (polymorphic-type body) →
  PolymorphicValueShape V
polymorphic-value-canonical
    (type-abstraction-typed
      {X = X} {V = V} W⊢ runtime environment
      fresh closed image typing) =
  type-abstraction-shape X V
polymorphic-value-canonical
    (forall-proxy-typed
      W⊢ runtime environment coercion value) =
  forall-proxy-shape _ _ _
polymorphic-value-canonical
    (generalized-typed
      W⊢ runtime environment coercion value) =
  generalized-shape _ _ _ _
