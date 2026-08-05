module proof.InterpreterLeftTypeAbstractionInstantiationSimulationProof where

-- File Charter:
--   * Proves source-only instantiation of an alpha-aware type abstraction.
--   * Combines its future-allocation certificate with unary source typing.
--   * Uses direct interpreter equations and no reduction semantics.

open import Agda.Builtin.Equality using (refl)

open import Interpreter
import Narrowing.InterpreterLeftTypeAbstractionNarrowing as
  AbstractionDefinition
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import proof.InterpreterTypeAbstractionInstantiationHelpers

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module Abstractions =
  AbstractionDefinition.LeftTypeAbstractionNarrowing
    interpreterNarrowingLeaves

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
left-type-abstraction-instantiation
    {W} {W′} {A} {θ} {body} {target} {X} {V} {V′}
    {R = R}
    θ-ok allocated-W⊢ W′⊢ abstraction V⊢ V′⊢ =
  simulation-pointwise
    type-abstraction-instantiation-computation
    (λ n → refl)
    (immediate-return-simulation
      (typed-value-narrowing
        (Abstractions.instantiate-related-left-type-abstraction
          abstraction extension-refl θ-ok)
        allocated-W⊢
        W′⊢
        (instantiated-type-abstraction-typing
          allocated-W⊢ V⊢)
        V′⊢))
