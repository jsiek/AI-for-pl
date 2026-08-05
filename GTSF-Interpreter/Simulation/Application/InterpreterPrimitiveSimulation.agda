module Simulation.Application.InterpreterPrimitiveSimulation where

-- File Charter:
--   * Public direct-simulation theorem for the interpreter primitive.
--   * States the semantic typing and value-narrowing requirements explicitly.
--   * Delegates canonical-form case analysis to the proof module.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTypedValueNarrowing
import Narrowing.InterpreterTermNarrowing as ITN
open import Primitives using (addℕ)
import proof.InterpreterPrimitiveSimulationCases as Proof
open import Types using (`ℕ)

open ITN.InterpreterValues
open ITN.RelatedWorlds

primitive-simulation :
  ∀ {W W′ V V′ U U′}
    {R : WorldRelation W W′} →
  ValueNarrowing R V V′ →
  ValueNarrowing R U U′ →
  ValueTyping W V (base-type `ℕ) →
  ValueTyping W′ V′ (base-type `ℕ) →
  ValueTyping W U (base-type `ℕ) →
  ValueTyping W′ U′ (base-type `ℕ) →
  TerminalSimulation ValueNarrowing R
    (fixedOutcome (applyPrimitive W addℕ V U))
    (fixedOutcome (applyPrimitive W′ addℕ V′ U′))
primitive-simulation =
  Proof.primitive-simulation

typed-primitive-simulation :
  ∀ {W W′ V V′ U U′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R V V′ →
  TypedValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R U U′ →
  TerminalSimulation
    (TypedValueResult (base-type `ℕ) (base-type `ℕ))
    R
    (fixedOutcome (applyPrimitive W addℕ V U))
    (fixedOutcome (applyPrimitive W′ addℕ V′ U′))
typed-primitive-simulation =
  Proof.typed-primitive-simulation
