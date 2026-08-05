module Runtime.InterpreterPolymorphicValueCanonicalCore where

-- File Charter:
--   * Defines the three semantic value shapes accepted by
--     `instantiateValue`.
--   * Contains no proof imports, interpreter execution, or reduction.

open import Interpreter using
  (Value; type-abstraction; forall-proxy; generalized)

data PolymorphicValueShape : Value → Set where
  type-abstraction-shape :
    ∀ X V →
    PolymorphicValueShape (type-abstraction X V)

  forall-proxy-shape :
    ∀ c θ V →
    PolymorphicValueShape (forall-proxy c θ V)

  generalized-shape :
    ∀ A c θ V →
    PolymorphicValueShape (generalized A c θ V)
