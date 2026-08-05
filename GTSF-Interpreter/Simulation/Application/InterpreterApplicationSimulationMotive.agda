module Simulation.Application.InterpreterApplicationSimulationMotive where

-- File Charter:
--   * Defines the typed simulation motive for semantic function application.
--   * Keeps the function and argument value relations explicit.
--   * Contains no simulation proof, recursive driver, or reduction semantics.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

ApplyValueSimulation : Set₂
ApplyValueSimulation =
  ∀ {W W′ A A′ B B′ V V′ U U′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′ →
  TypedValueNarrowing A A′ R U U′ →
  TerminalSimulation (TypedValueResult B B′) R
    (applyValue W V U)
    (applyValue W′ V′ U′)
