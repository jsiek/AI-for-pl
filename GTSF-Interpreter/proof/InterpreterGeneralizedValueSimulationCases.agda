module proof.InterpreterGeneralizedValueSimulationCases where

-- File Charter:
--   * Identifies generalized instantiation with one guarded coercion call.
--   * Transports paired coercion simulation through that constructor guard.
--   * Uses only direct interpreter equations and simulation algebra.

open import Data.List using (_∷_)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterGeneralizedValueComputation using
  (generalized-value-computation-eq)
open import proof.InterpreterGuardSimulation using (guard-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

paired-generalized-value-instantiation :
  ∀ {W W′ α α′ A A′ c c′ θ θ′ V V′}
    {result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation result R
    (coerceValue W (seal-name α ∷ θ) c V)
    (coerceValue W′ (seal-name α′ ∷ θ′) c′ V′) →
  TerminalSimulation result R
    (instantiateValue W α (generalized A c θ V))
    (instantiateValue W′ α′ (generalized A′ c′ θ′ V′))
paired-generalized-value-instantiation
    {W} {W′} {α} {α′} {A} {A′} {c} {c′}
    {θ} {θ′} {V} {V′}
    coercion-simulation =
  simulation-pointwise
    (λ n →
      generalized-value-computation-eq
        {W = W} {α = α} {A = A} {c = c} {θ = θ}
        {V = V} n)
    (λ n →
      generalized-value-computation-eq
        {W = W′} {α = α′} {A = A′} {c = c′}
        {θ = θ′} {V = V′} n)
    (guard-simulation coercion-simulation)
