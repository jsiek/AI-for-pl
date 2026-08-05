module proof.InterpreterRightGeneralizedValueSimulationCases where

-- File Charter:
--   * Simulates target-only generalized-value instantiation.
--   * Adds the generalized constructor's fuel guard on the target only.
--   * Uses direct interpreter equations and terminal-simulation algebra.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterGeneralizedValueComputation using
  (generalized-value-computation-eq)
open import proof.InterpreterOneSidedGuardSimulation using
  (right-guard-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

right-generalized-value-instantiation :
  ∀ {W W′ α′ A′ c′ θ′ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (immediateReturn W V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′) →
  TerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
right-generalized-value-instantiation
    {W} {W′} {α′} {A′} {c′} {θ′} {V} {V′}
    coercion-simulation =
  simulation-pointwise
    (λ n → refl)
    (λ n →
      generalized-value-computation-eq
        {W = W′} {α = α′} {A = A′} {c = c′} {θ = θ′}
        {V = V′} n)
    (right-guard-simulation coercion-simulation)
