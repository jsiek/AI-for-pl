module Simulation.Core.InterpreterTypedSimulation where

-- File Charter:
--   * Public bridge from value-only terminal simulation to typed terminal
--     simulation.
--   * States the unary outcome-typing requirements explicitly.
--   * Delegates result extraction to the focused proof module.

open import Interpreter using (World)
open import Typing.InterpreterSemanticTypingCore using
  (OutcomeTyping; SemanticType)
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTypedValueNarrowing
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterTypedSimulationProof as Proof

open ITN.InterpreterValues
open ITN.RelatedWorlds

typed-result-simulation :
  ∀ {W W′ A B}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  (∀ n → OutcomeTyping W A (left n)) →
  (∀ n → OutcomeTyping W′ B (right n)) →
  TerminalSimulation (TypedValueResult A B) R left right
typed-result-simulation =
  Proof.typed-result-simulation
