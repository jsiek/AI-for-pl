module proof.InterpreterTypeAbstractionInstantiationSimulationProof where

-- File Charter:
--   * Proves paired instantiation of alpha-aware type abstractions.
--   * Combines direct interpreter equations, unary instantiation typing, and
--     the abstraction certificate at one related allocation boundary.
--   * Uses no small-step or reduction-derived theorem.

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
import Narrowing.InterpreterTypeAbstractionNarrowing as AbstractionDefinition
open import Narrowing.InterpreterTypedValueNarrowing
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import proof.InterpreterTypeAbstractionInstantiationHelpers

open Narrowing.InterpreterTermNarrowing.InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module Abstractions =
  AbstractionDefinition.TypeAbstractionNarrowing
    interpreterNarrowingLeaves

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
paired-type-abstraction-instantiation
    {W} {W′} {A} {A′} {θ} {θ′}
    {body} {body′} {X} {X′} {V} {V′}
    A~A′ θ~θ′ allocated-W⊢ allocated-W′⊢
    abstraction V⊢ V′⊢ =
  simulation-pointwise
    type-abstraction-instantiation-computation
    type-abstraction-instantiation-computation
    (immediate-return-simulation
      (typed-value-narrowing
        (Abstractions.instantiate-related-type-abstraction
          abstraction A~A′ θ~θ′)
        allocated-W⊢
        allocated-W′⊢
        (instantiated-type-abstraction-typing
          allocated-W⊢ V⊢)
        (instantiated-type-abstraction-typing
          allocated-W′⊢ V′⊢)))
