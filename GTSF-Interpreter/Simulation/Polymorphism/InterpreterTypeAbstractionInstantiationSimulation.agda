module
  Simulation.Polymorphism.InterpreterTypeAbstractionInstantiationSimulation
  where

-- File Charter:
--   * Public paired `instantiateValue` simulation for type abstractions.
--   * Eliminates the alpha-aware abstraction certificate at the exact
--     interpreter allocation and returns semantically typed bodies.
--   * Delegates computation and typing details to a reduction-free proof.

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import proof.InterpreterTypeAbstractionInstantiationSimulationProof as Proof

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-type-abstraction-instantiation :
  ∀ {W W′ A A′ θ θ′ body body′ X X′ V V′}
    {R : WorldRelation W W′} →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  WorldTyping (allocate W A θ) →
  WorldTyping (allocate W′ A′ θ′) →
  TypeAbstractionNarrowing R X X′ V V′ →
  ValueTyping W (type-abstraction X V)
    (polymorphic-type body) →
  ValueTyping W′ (type-abstraction X′ V′)
    (polymorphic-type body′) →
  TerminalSimulation
    (TypedValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-both R A~A′ θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′)
      (type-abstraction X′ V′))
paired-type-abstraction-instantiation =
  Proof.paired-type-abstraction-instantiation
