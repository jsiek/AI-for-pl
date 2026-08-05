module proof.InterpreterPrimitiveTermSimulationCases where

-- File Charter:
--   * Composes the two operand simulations with primitive-value simulation.
--   * Rebuilds synchronized runtime evidence after every returned-world
--     extension and keeps both operand typings available.
--   * Uses direct interpreter equations only; no reduction semantics occur.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

open import ImprecisionWf using (idι)
open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Simulation.Application.InterpreterPrimitiveSimulation
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Simulation.Core.InterpreterTermSimulationMotive
open import Simulation.Core.InterpreterTermSimulationTyping
open import Narrowing.InterpreterTypedValueNarrowing
open import Narrowing.InterpreterTypedValueNarrowingProperties
import NuTerms as N
open import Primitives using (addℕ)
open import proof.InterpreterPrimitiveTermSimulationTail
open import proof.InterpreterSequenceSimulation using
  (chain-simulation; sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

primitive-tail-simulation :
  ∀ {W W′ γ γ′ θ θ′ M M′ V V′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing
    (base-type `ℕ) (base-type `ℕ) R V V′ →
  TerminalSimulation
    (TypedValueResult (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ M′) →
  (∀ n →
    OutcomeTyping W′ (base-type `ℕ)
      (interpret W′ γ′ θ′ M′ n)) →
  TerminalSimulation
    (TypedValueResult (base-type `ℕ) (base-type `ℕ))
    R
    (primitive-tail W γ θ M V)
    (primitive-tail W′ γ′ θ′ M′ V′)
primitive-tail-simulation
    {W} {W′} {γ} {γ′} {θ} {θ′} {M} {M′} {V} {V′}
    {R = R} V~V′ M-simulation right-M-typing =
  chain-simulation
    {W = W} {W′ = W′} {R = R}
    {left-head = interpret W γ θ M}
    {right-head = interpret W′ γ′ θ′ M′}
    {left-continuation = primitive-continuation V}
    {right-continuation = primitive-continuation V′}
    M-simulation
    (λ R≤S Q~Q′ →
      typed-primitive-simulation
        (typed-value-narrowing-weaken R≤S
          (left-world-typed Q~Q′)
          (right-world-typed Q~Q′)
          V~V′)
        Q~Q′)
    (λ U Q {n} {o} terminal eq k →
      primitive-continuation-stable V U Q
        {n = n} {o = o} terminal eq k)
    (λ U′ Q′ {n} {o} terminal eq k →
      primitive-continuation-stable V′ U′ Q′
        {n = n} {o = o} terminal eq k)
    (λ { {n} {Z′} {e} eq →
      primitive-tail-error-impossible
        {W = W′} {γ = γ′} {θ = θ′} {M = M′} {V = V′}
        (right-value-typed V~V′) right-M-typing
        {n = n} {Z = Z′} {e = e} eq
      })

primitive-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ L L′ M M′}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.⊕[ addℕ ] M)
    (L′ N.⊕[ addℕ ] M′)
    (‵ `ℕ) (‵ `ℕ) idι →
  InterpreterTermSimulation
    Φ Δᴸ Δᴿ ρ γᵀ L L′
    (‵ `ℕ) (‵ `ℕ) idι →
  InterpreterTermSimulation
    Φ Δᴸ Δᴿ ρ γᵀ M M′
    (‵ `ℕ) (‵ `ℕ) idι →
  TerminalSimulation
    (TypedValueResult (base-type `ℕ) (base-type `ℕ))
    R
    (interpret W γ θ (L N.⊕[ addℕ ] M))
    (interpret W′ γ′ θ′ (L′ N.⊕[ addℕ ] M′))
primitive-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment terms L-simulation M-simulation
    with primitive-open-operands terms
primitive-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment terms L-simulation M-simulation
    | L-terms , M-terms =
  simulation-pointwise
    primitive-computation-eq
    primitive-computation-eq
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = interpret W γ θ L}
      {right-head = interpret W′ γ′ θ′ L′}
      {left-continuation =
        λ U V → primitive-tail U γ θ M V}
      {right-continuation =
        λ U′ V′ → primitive-tail U′ γ′ θ′ M′ V′}
      (L-simulation runtime environment L-terms)
      (λ R≤S V~V′ →
        primitive-tail-simulation V~V′
          (M-simulation
            (runtime-narrowing-weaken R≤S
              (left-world-typed V~V′)
              (right-world-typed V~V′)
              runtime)
            (environment-realization-weaken R≤S
              (left-world-typed V~V′)
              (right-world-typed V~V′)
              environment)
            (open-interpreter-narrowing-world-weaken R≤S M-terms))
          (target-interpret-typing
            (environment-realization-weaken R≤S
              (left-world-typed V~V′)
              (right-world-typed V~V′)
              environment)
            (open-interpreter-narrowing-world-weaken R≤S M-terms)))
      (λ U V {n} {o} terminal eq k →
        primitive-tail-stable
          {W = U} {γ = γ} {θ = θ} {M = M} {V = V}
          {n = n} {o = o} terminal eq k)
      (λ U′ V′ {n} {o} terminal eq k →
        primitive-tail-stable
          {W = U′} {γ = γ′} {θ = θ′} {M = M′} {V = V′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} eq →
        outcome-typing-excludes-error
          (target-interpret-typing environment terms n)
          (trans (primitive-computation-eq n) eq)
        }))
