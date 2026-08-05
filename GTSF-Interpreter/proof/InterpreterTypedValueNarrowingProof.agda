module proof.InterpreterTypedValueNarrowingProof where

-- File Charter:
--   * Proves related-world weakening for typed value narrowing.
--   * Transports both unary semantic typings and the shared value relation.
--   * Contains no interpreter call or reduction semantics.

open import Narrowing.InterpreterEnvironmentNarrowing
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationContextProperties
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module EnvironmentProperties =
  Narrowing.InterpreterEnvironmentNarrowing.EnvironmentNarrowing
    interpreterNarrowingLeaves

typed-value-narrowing-weaken :
  ∀ {W W′ U U′ A B V V′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Narrowing.InterpreterTermNarrowing.RelatedWorlds.WorldExtension R S →
  WorldTyping U →
  WorldTyping U′ →
  TypedValueNarrowing A B R V V′ →
  TypedValueNarrowing A B S V V′
typed-value-narrowing-weaken R≤S U⊢ U′⊢ typed =
  typed-value-narrowing
    (EnvironmentProperties.value-narrowing-weaken R≤S
      (values-narrow typed))
    U⊢
    U′⊢
    (semantic-value-world-weaken
      (left-world-extension R≤S) U⊢
      (left-value-typed typed))
    (semantic-value-world-weaken
      (right-world-extension R≤S) U′⊢
      (right-value-typed typed))
