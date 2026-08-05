module Simulation.Coercion.InterpreterCoercionOneSidedSequenceSimulation where

-- File Charter:
--   * Exposes source-only and target-only coercion-sequence simulations.
--   * States both recursive phase simulations directly.
--   * Keeps target error freedom explicit only for target-side sequencing.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import Coercions
open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterCoercionOneSidedSequenceSimulationProof as Proof

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
left-sequence-coercion-simulation =
  Proof.left-sequence-coercion-simulation

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
right-sequence-coercion-simulation =
  Proof.right-sequence-coercion-simulation
