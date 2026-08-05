module Examples.InterpreterForallProxySimulationExamples where

-- File Charter:
--   * Checks the direct forall-proxy computation by normalization.
--   * Exercises underlying type abstraction and the stored forall coercion.
--   * Uses a first-order result so the complete proxy path is observable.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Nat using (zero; suc)

import Coercions
open import Interpreter
open import Simulation.Polymorphism.InterpreterForallProxySimulation
open import Typing.InterpreterForallProxyTyping
open import Primitives using (κℕ)
open import Types

Nat : Ty
Nat =
  ‵ `ℕ

proxy-world : World
proxy-world =
  allocate emptyWorld Nat []

identity-forall-proxy : Value
identity-forall-proxy =
  forall-proxy
    (Coercions.id Nat)
    []
    (type-abstraction
      (type-name zero)
      (constant (κℕ 7)))

identity-forall-proxy-result :
  instantiateValue proxy-world
    (freshSealName emptyWorld)
    identity-forall-proxy
    (suc (suc zero)) ≡
  returned proxy-world (constant (κℕ 7))
identity-forall-proxy-result =
  refl
