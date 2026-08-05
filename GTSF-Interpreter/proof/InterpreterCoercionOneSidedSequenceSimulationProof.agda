module proof.InterpreterCoercionOneSidedSequenceSimulationProof where

-- File Charter:
--   * Composes one-sided coercion sequences through explicit computations.
--   * Keeps the inactive endpoint at an immediate return.
--   * Uses terminal stability and unary target error freedom only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (trans)

import Coercions
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComputation
open import Core.InterpreterFuel using (coerceValue-terminal-stable)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterOneSidedSequenceSimulation using
  (left-sequence-simulation; right-sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)

open ITN.RelatedWorlds

left-sequence-coercion-simulation :
  ∀ {W W′ θ c d V V′}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation head-result R
    (coerceValue W θ c V)
    (immediateReturn W′ V′) →
  (∀ {U U′ Q Q′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S Q Q′ →
    TerminalSimulation result S
      (coerceValue U θ d Q)
      (immediateReturn U′ Q′)) →
  TerminalSimulation result R
    (coerceValue W θ (c Coercions.︔ d) V)
    (immediateReturn W′ V′)
left-sequence-coercion-simulation
    {W} {W′} {θ} {c} {d} {V} {V′} {R = R}
    head-simulation continuation-simulation =
  simulation-pointwise
    (coerce-sequence-computation
      {W = W} {θ = θ} {c = c} {d = d} {V = V})
    (λ n → refl)
    (left-sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = coerceValue W θ c V}
      {right-head = immediateReturn W′ V′}
      {left-continuation =
        λ U Q → coerceValue U θ d Q}
      head-simulation
      continuation-simulation
      (λ U Q {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U} {θ = θ} {c = d} {V = Q}
          {n = n} {o = o} terminal eq k))

right-sequence-coercion-simulation :
  ∀ {W W′ θ′ c′ d′ V V′}
    {head-result result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation head-result R
    (immediateReturn W V)
    (coerceValue W′ θ′ c′ V′) →
  (∀ {U U′ Q Q′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S Q Q′ →
    TerminalSimulation result S
      (immediateReturn U Q)
      (coerceValue U′ θ′ d′ Q′)) →
  (∀ {n Z′ e} →
    coerceValue W′ θ′ (c′ Coercions.︔ d′) V′ n ≡
      failed Z′ e →
    ⊥) →
  TerminalSimulation result R
    (immediateReturn W V)
    (coerceValue W′ θ′ (c′ Coercions.︔ d′) V′)
right-sequence-coercion-simulation
    {W} {W′} {θ′} {c′} {d′} {V} {V′} {R = R}
    head-simulation continuation-simulation
    target-sequence-error-free =
  simulation-pointwise
    (λ n → refl)
    (coerce-sequence-computation
      {W = W′} {θ = θ′} {c = c′} {d = d′} {V = V′})
    (right-sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = immediateReturn W V}
      {right-head = coerceValue W′ θ′ c′ V′}
      {right-continuation =
        λ U′ Q′ → coerceValue U′ θ′ d′ Q′}
      head-simulation
      continuation-simulation
      (λ U′ Q′ {n} {o} terminal eq k →
        coerceValue-terminal-stable
          {W = U′} {θ = θ′} {c = d′} {V = Q′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} {Z′} {e} eq →
        target-sequence-error-free
          {n = n} {Z′ = Z′} {e = e}
          (trans
            (coerce-sequence-computation
              {W = W′} {θ = θ′}
              {c = c′} {d = d′} {V = V′} n)
            eq)
        }))
