module Simulation.Framed.InterpreterFramedTypeTransport where

-- File Charter:
--   * Transports typed value narrowing across paired and left-only static
--     allocation frames.
--   * Isolates the semantic interpretation equation for weakening.
--   * Contains no interpreter call, recursion, or reduction result.

open import Data.List using (_∷_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowingProperties using
  (typed-value-type-transport)
open import Narrowing.InterpreterOperationalValueNarrowing using
  (OperationalValueNarrowing)
open import Typing.InterpreterSemanticTypingCore using
  (nominal-type; semanticEnvironment; ⟦_⟧[_])
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using
  (TypedValueNarrowing)
open import proof.InterpreterOperationalEnvironmentLift using
  (operational-value-type-transport)
open import proof.InterpreterSemanticTypingProperties using
  (interpret-weaken)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-typed-value-unlift :
  ∀ {W W′ θ θ′ α α′ A A′ V V′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ ⇑ᵗ A′ ⟧[ seal-name α′ ∷ θ′ ] R V V′ →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
paired-typed-value-unlift
    {θ = θ} {θ′ = θ′} {α = α} {α′ = α′} {A = A} {A′ = A′} =
  typed-value-type-transport
    (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A)
    (interpret-weaken
      (nominal-type (seal-name α′))
      (semanticEnvironment θ′) A′)

paired-typed-value-lift :
  ∀ {W W′ θ θ′ α α′ A A′ V V′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  TypedValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ ⇑ᵗ A′ ⟧[ seal-name α′ ∷ θ′ ] R V V′
paired-typed-value-lift
    {θ = θ} {θ′ = θ′} {α = α} {α′ = α′} {A = A} {A′ = A′} =
  typed-value-type-transport
    (sym (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A))
    (sym (interpret-weaken
      (nominal-type (seal-name α′))
      (semanticEnvironment θ′) A′))

paired-operational-value-unlift :
  ∀ {W W′ θ θ′ α α′ A A′ V V′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ ⇑ᵗ A′ ⟧[ seal-name α′ ∷ θ′ ] R V V′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
paired-operational-value-unlift
    {θ = θ} {θ′ = θ′} {α = α} {α′ = α′}
    {A = A} {A′ = A′} =
  operational-value-type-transport
    (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A)
    (interpret-weaken
      (nominal-type (seal-name α′))
      (semanticEnvironment θ′) A′)

left-typed-value-unlift :
  ∀ {W W′ θ θ′ α A A′ V V′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ A′ ⟧[ θ′ ] R V V′ →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
left-typed-value-unlift {θ = θ} {α = α} {A = A} =
  typed-value-type-transport
    (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A)
    refl

left-typed-value-lift :
  ∀ {W W′ θ θ′ α A A′ V V′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′ →
  TypedValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ A′ ⟧[ θ′ ] R V V′
left-typed-value-lift {θ = θ} {α = α} {A = A} =
  typed-value-type-transport
    (sym (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A))
    refl

left-operational-value-unlift :
  ∀ {W W′ θ θ′ α A A′ V V′}
    {R : WorldRelation W W′} →
  OperationalValueNarrowing
    ⟦ ⇑ᵗ A ⟧[ seal-name α ∷ θ ]
    ⟦ A′ ⟧[ θ′ ] R V V′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ A′ ⟧[ θ′ ] R V V′
left-operational-value-unlift {θ = θ} {α = α} {A = A} =
  operational-value-type-transport
    (interpret-weaken
      (nominal-type (seal-name α))
      (semanticEnvironment θ) A)
    refl
