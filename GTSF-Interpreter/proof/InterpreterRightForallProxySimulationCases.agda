module proof.InterpreterRightForallProxySimulationCases where

-- File Charter:
--   * Composes target-only instantiation of a forall proxy.
--   * Runs payload instantiation and the stored coercion only on the target.
--   * Uses direct interpreter equations and unary target error freedom.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using (_∷_)
open import Relation.Binary.PropositionalEquality using (trans)

open import Interpreter
open import Core.InterpreterFuel using (coerceValue-terminal-stable)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterForallProxyComputation using
  (forall-proxy-computation-eq)
open import proof.InterpreterOneSidedSequenceSimulation using
  (right-sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

right-forall-proxy-instantiation :
  ∀ {W W′ α′ θ′ c′ V V′}
    {instantiation-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  (instantiation-simulation :
    TerminalSimulation instantiation-result R
      (immediateReturn W V)
      (instantiateValue W′ α′ V′)) →
  (coercion-simulation :
    ∀ {Z Z′ U U′}
      {S : WorldRelation Z Z′} →
    WorldExtension R S →
    instantiation-result S U U′ →
    TerminalSimulation result S
      (immediateReturn Z U)
      (coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′)) →
  (∀ {n Z′ e} →
    instantiateValue W′ α′ (forall-proxy c′ θ′ V′) n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (immediateReturn W V)
    (instantiateValue W′ α′ (forall-proxy c′ θ′ V′))
right-forall-proxy-instantiation
    {W} {W′} {α′} {θ′} {c′} {V} {V′} {R = R}
    instantiation-simulation coercion-simulation
    target-instantiation-error-free =
  simulation-pointwise
    (λ n → refl)
    (λ n →
      forall-proxy-computation-eq
        {W = W′} {α = α′} {θ = θ′} {c = c′} {V = V′} n)
    (right-sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = immediateReturn W V}
      {right-head = instantiateValue W′ α′ V′}
      {right-continuation =
        λ Z′ U′ →
          coerceValue Z′ (seal-name α′ ∷ θ′) c′ U′}
      instantiation-simulation
      coercion-simulation
      (λ Z′ U′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = Z′} {θ = seal-name α′ ∷ θ′}
          {c = c′} {V = U′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} {Z′} {e} eq →
        target-instantiation-error-free
          {n = n} {Z′ = Z′} {e = e}
          (trans
            (forall-proxy-computation-eq
              {W = W′} {α = α′} {θ = θ′}
              {c = c′} {V = V′} n)
            eq)
        }))
