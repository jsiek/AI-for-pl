module proof.InterpreterForallProxyComputation where

-- File Charter:
--   * Exposes the direct interpreter equation for forall-proxy instantiation.
--   * Makes the wrapped-value and stored-coercion phases explicit.
--   * Contains no simulation or small-step reasoning.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult

forall-proxy-computation-eq :
  ∀ {W α θ c V} n →
  instantiateValue W α (forall-proxy c θ V) n ≡
  sequence W
    (instantiateValue W α V)
    (λ Z U → coerceValue Z (seal-name α ∷ θ) c U)
    n
forall-proxy-computation-eq zero =
  refl
forall-proxy-computation-eq
    {W} {α} {θ} {c} {V} (suc n)
    with instantiateValue W α V n
forall-proxy-computation-eq (suc n) | timed Z =
  refl
forall-proxy-computation-eq (suc n) | blamed Z =
  refl
forall-proxy-computation-eq (suc n) | failed Z e =
  refl
forall-proxy-computation-eq (suc n) | returned Z U =
  refl
