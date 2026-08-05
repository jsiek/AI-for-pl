module Simulation.Polymorphism.InterpreterInstantiationSimulationMotive where

-- File Charter:
--   * Defines typed paired and source-only motives for `instantiateValue`.
--   * Keeps the allocating world relation explicit, since type-abstraction
--     narrowing is eliminated exactly at that allocation boundary.
--   * Contains no recursive driver, interpreter proof, or reduction semantics.

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

PairedInstantiateValueSimulation : Set₂
PairedInstantiateValueSimulation =
  ∀ {W W′ A A′ θ θ′ body body′ V V′}
    {R : WorldRelation W W′} →
  (A~A′ : InterpreterTypeNarrowing A A′) →
  (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
  WorldTyping (allocate W A θ) →
  WorldTyping (allocate W′ A′ θ′) →
  TypedValueNarrowing
    (polymorphic-type body) (polymorphic-type body′)
    R V V′ →
  TerminalSimulation
    (TypedValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W′))) body′))
    (allocate-both R A~A′ θ~θ′)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (instantiateValue
      (allocate W′ A′ θ′) (freshSealName W′) V′)

LeftInstantiateValueSimulation : Set₂
LeftInstantiateValueSimulation =
  ∀ {W W′ A θ body target V V′}
    {R : WorldRelation W W′} →
  (θ-ok : TypeEnvironmentScoped W θ) →
  WorldTyping (allocate W A θ) →
  WorldTyping W′ →
  TypedValueNarrowing
    (polymorphic-type body) target R V V′ →
  TerminalSimulation
    (TypedValueResult
      (instantiateSemantic
        (nominal-type (seal-name (freshSealName W))) body)
      target)
    (allocate-left-dynamic {A = A} R θ-ok)
    (instantiateValue
      (allocate W A θ) (freshSealName W) V)
    (immediateReturn W′ V′)
