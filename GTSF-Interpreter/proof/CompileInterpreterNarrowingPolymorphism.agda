module proof.CompileInterpreterNarrowingPolymorphism where

-- File Charter:
--   * Supplies compiler-image constructors for raw type abstractions and
--     explicit interpreter instantiation.
--   * Requires syntactic value evidence at every raw type abstraction.
--   * Contains no runtime bullet or reduction rule.

open import Coercions using (Coercion)
open import InterpreterTermNarrowingCore
import NuTerms as N
open import Types

compiled-type-abstraction-interpreter-term :
  ∀ {V} →
  N.Value V →
  InterpreterTerm V →
  InterpreterTerm (N.Λ V)
compiled-type-abstraction-interpreter-term =
  type-abstraction-term

compiled-instantiation-interpreter-term :
  ∀ {A L c} →
  InterpreterTerm L →
  InterpreterTerm (N.ν A L c)
compiled-instantiation-interpreter-term =
  instantiation-term

compiled-paired-type-abstraction-shape :
  ∀ {V V′} →
  N.Value V →
  N.Value V′ →
  InterpreterTerm V →
  InterpreterTerm V′ →
  InterpreterTermShape (N.Λ V) (N.Λ V′)
compiled-paired-type-abstraction-shape =
  paired-type-abstraction-shape

compiled-left-type-abstraction-shape :
  ∀ {V N′} →
  N.Value V →
  InterpreterTerm V →
  InterpreterTerm N′ →
  InterpreterTermShape (N.Λ V) N′
compiled-left-type-abstraction-shape =
  left-type-abstraction-shape

compiled-paired-instantiation-shape :
  ∀ {A A′ L L′ c c′} →
  InterpreterTermShape L L′ →
  InterpreterTermShape (N.ν A L c) (N.ν A′ L′ c′)
compiled-paired-instantiation-shape =
  paired-instantiation-shape

compiled-left-instantiation-shape :
  ∀ {A L L′ c} →
  InterpreterTermShape L L′ →
  InterpreterTermShape (N.ν A L c) L′
compiled-left-instantiation-shape =
  left-instantiation-shape
