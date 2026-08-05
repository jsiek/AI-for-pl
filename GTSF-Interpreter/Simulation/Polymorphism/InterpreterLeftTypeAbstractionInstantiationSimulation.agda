module
  Simulation.Polymorphism.InterpreterLeftTypeAbstractionInstantiationSimulation
  where

-- File Charter:
--   * Public source-only `instantiateValue` simulation for type abstractions.
--   * Eliminates the extensional left abstraction certificate at the actual
--     interpreter allocation and returns a typed substituted source body.
--   * Delegates the direct computation proof to a reduction-free module.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
import proof.InterpreterLeftTypeAbstractionInstantiationSimulationProof
  as Proof

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-type-abstraction-instantiation :
  ∀ {W W′ A θ body target X V V′}
    {R : WorldRelation W W′} →
  (θ-ok : TypeEnvironmentScoped W θ) →
  WorldTyping (allocate W A θ) →
  WorldTyping W′ →
  LeftTypeAbstractionNarrowing R X V V′ →
  ValueTyping W (type-abstraction X V)
    (polymorphic-type body) →
  ValueTyping W′ V′ target →
  TerminalSimulation
    (TypedValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      target)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W)
      (type-abstraction X V))
    (immediateReturn W′ V′)
left-type-abstraction-instantiation =
  Proof.left-type-abstraction-instantiation
