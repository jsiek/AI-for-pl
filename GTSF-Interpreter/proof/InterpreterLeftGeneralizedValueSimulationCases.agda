module proof.InterpreterLeftGeneralizedValueSimulationCases where

-- File Charter:
--   * Simulates source-only generalized-value instantiation.
--   * Adds the generalized constructor's fuel guard on the source only.
--   * Uses direct interpreter equations and terminal-simulation algebra.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterGeneralizedValueComputation using
  (generalized-value-computation-eq)
open import proof.InterpreterOneSidedGuardSimulation using
  (left-guard-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

left-generalized-value-instantiation :
  ∀ {W W′ α A c θ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (immediateReturn W′ V′) →
  TerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (immediateReturn W′ V′)
left-generalized-value-instantiation
    {W} {W′} {α} {A} {c} {θ} {V} {V′}
    coercion-simulation =
  simulation-pointwise
    (λ n →
      generalized-value-computation-eq
        {W = W} {α = α} {A = A} {c = c} {θ = θ}
        {V = V} n)
    (λ n → refl)
    (left-guard-simulation coercion-simulation)
