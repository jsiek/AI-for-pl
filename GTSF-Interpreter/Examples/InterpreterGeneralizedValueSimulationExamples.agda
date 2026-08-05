module Examples.InterpreterGeneralizedValueSimulationExamples where

-- File Charter:
--   * Checks direct generalized-value instantiation by normalization.
--   * Exercises the outer constructor guard and stored coercion call.
--   * Uses a first-order result so the complete path is observable.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)

import Coercions
open import Interpreter
open import Simulation.Polymorphism.InterpreterGeneralizedValueSimulation
open import Typing.InterpreterGeneralizedValueTyping
open import Primitives using (κℕ)
open import Types

Nat : Ty
Nat =
  ‵ `ℕ

generalized-world : World
generalized-world =
  allocate emptyWorld Nat []

identity-generalized-value : Value
identity-generalized-value =
  generalized Nat
    (Coercions.id Nat)
    []
    (constant (κℕ 7))

identity-generalized-value-result :
  instantiateValue generalized-world
    (freshSealName emptyWorld)
    identity-generalized-value
    (suc (suc zero)) ≡
  returned generalized-world (constant (κℕ 7))
identity-generalized-value-result =
  refl
