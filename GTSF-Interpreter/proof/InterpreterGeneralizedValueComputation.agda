module proof.InterpreterGeneralizedValueComputation where

-- File Charter:
--   * Exposes the direct interpreter equation for generalized instantiation.
--   * Identifies its stored coercion underneath one constructor-fuel guard.
--   * Contains no simulation or small-step reasoning.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult

generalized-value-computation-eq :
  ∀ {W α A c θ V} n →
  instantiateValue W α (generalized A c θ V) n ≡
  guard W (coerceValue W (seal-name α ∷ θ) c V) n
generalized-value-computation-eq zero =
  refl
generalized-value-computation-eq (suc n) =
  refl
