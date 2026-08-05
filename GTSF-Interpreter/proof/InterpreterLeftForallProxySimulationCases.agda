module proof.InterpreterLeftForallProxySimulationCases where

-- File Charter:
--   * Composes source-only instantiation of a forall proxy.
--   * Runs the wrapped-value and stored-coercion phases only on the source.
--   * Uses direct interpreter equations and terminal-simulation sequencing.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)

open import Interpreter
open import Core.InterpreterFuel using (coerceValue-terminal-stable)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterForallProxyComputation using
  (forall-proxy-computation-eq)
open import proof.InterpreterOneSidedSequenceSimulation using
  (left-sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

left-forall-proxy-instantiation :
  ∀ {W W′ α θ c V V′}
    {instantiation-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (instantiation-simulation :
    TerminalSimulation instantiation-result R
      (instantiateValue W α V)
      (immediateReturn W′ V′)) →
  (coercion-simulation :
    ∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    instantiation-result S U U′ →
    TerminalSimulation result S
      (coerceValue Z (seal-name α ∷ θ) c U)
      (immediateReturn Z′ U′)) →
  TerminalSimulation result R
    (instantiateValue W α (forall-proxy c θ V))
    (immediateReturn W′ V′)
left-forall-proxy-instantiation
    {W} {W′} {α} {θ} {c} {V} {V′} {R = R}
    instantiation-simulation coercion-simulation =
  simulation-pointwise
    (λ n →
      forall-proxy-computation-eq
        {W = W} {α = α} {θ = θ} {c = c} {V = V} n)
    (λ n → refl)
    (left-sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = instantiateValue W α V}
      {right-head = immediateReturn W′ V′}
      {left-continuation =
        λ Z U → coerceValue Z (seal-name α ∷ θ) c U}
      instantiation-simulation
      coercion-simulation
      (λ Z U {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z} {θ = seal-name α ∷ θ} {c = c} {V = U}
          {n = n} {o = o} terminal eq k))
