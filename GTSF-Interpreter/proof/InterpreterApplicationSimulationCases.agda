module proof.InterpreterApplicationSimulationCases where

-- File Charter:
--   * Composes function, argument, and semantic-application simulations.
--   * Joins independently delayed observations and rebuilds synchronized
--     runtime evidence after each returned-world extension.
--   * Uses direct interpreter equations only; no reduction semantics occur.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (trans)

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Application.InterpreterApplicationSimulationMotive
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Core.InterpreterFuel using
  (applyValue-terminal-stable)
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
open import proof.InterpreterApplicationTail
open import proof.InterpreterSequenceSimulation using
  (chain-simulation; sequence-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

application-tail-simulation :
  ∀ {W W′ γ γ′ θ θ′ M M′ V V′ A A′ B B′}
    {R : WorldRelation W W′} →
  TypedValueNarrowing (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′ →
  TerminalSimulation (TypedValueResult A A′) R
    (interpret W γ θ M)
    (interpret W′ γ′ θ′ M′) →
  (∀ n → OutcomeTyping W′ A′ (interpret W′ γ′ θ′ M′ n)) →
  ApplyValueSimulation →
  TerminalSimulation (TypedValueResult B B′) R
    (application-tail W γ θ M V)
    (application-tail W′ γ′ θ′ M′ V′)
application-tail-simulation
    {W} {W′} {γ} {γ′} {θ} {θ′} {M} {M′}
    {V} {V′} {R = R}
    V~V′ M-simulation right-M-typing
    apply-simulation =
  chain-simulation
    {W = W} {W′ = W′} {R = R}
    {left-head = interpret W γ θ M}
    {right-head = interpret W′ γ′ θ′ M′}
    {left-continuation = application-continuation V}
    {right-continuation = application-continuation V′}
    M-simulation
    (λ R≤S Q~Q′ →
      apply-simulation
        (typed-value-narrowing-weaken R≤S
          (left-world-typed Q~Q′)
          (right-world-typed Q~Q′)
          V~V′)
        Q~Q′)
    (λ U Q {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = U} {V = V} {U = Q}
        {n = n} {o = o} terminal eq k)
    (λ U′ Q′ {n} {o} terminal eq k →
      applyValue-terminal-stable
        {W = U′} {V = V′} {U = Q′}
        {n = n} {o = o} terminal eq k)
    (λ { {n} {Z′} {e} eq →
      application-tail-error-impossible
        (right-value-typed V~V′)
        right-M-typing
        {n = n} {Z = Z′} {e = e} eq
      })

application-term-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ L L′ M M′ B B′ pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ
    (L N.· M) (L′ N.· M′) B B′ pB →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ L L′
      (A ⇒ B) (A′ ⇒ B′) (pA ↦ pB)) →
  (∀ {A A′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
    InterpreterTermSimulation
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A A′ pA) →
  ApplyValueSimulation →
  TerminalSimulation
    (TypedValueResult ⟦ B ⟧[ θ ] ⟦ B′ ⟧[ θ′ ])
    R
    (interpret W γ θ (L N.· M))
    (interpret W′ γ′ θ′ (L′ N.· M′))
application-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment terms L-simulation M-simulation
    apply-simulation
    with application-open-operands terms
application-term-simulation
    {W} {W′} {Φ} {Δᴸ} {Δᴿ} {ρ} {γᵀ}
    {θ} {θ′} {γ} {γ′} {L} {L′} {M} {M′}
    {R = R} {runtime = runtime}
    environment terms L-simulation M-simulation
    apply-simulation
    | A , A′ , pA , L-terms , M-terms =
  simulation-pointwise
    application-computation-eq
    application-computation-eq
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = interpret W γ θ L}
      {right-head = interpret W′ γ′ θ′ L′}
      {left-continuation =
        λ U V → application-tail U γ θ M V}
      {right-continuation =
        λ U′ V′ → application-tail U′ γ′ θ′ M′ V′}
      (L-simulation runtime environment L-terms)
      (λ R≤S V~V′ →
        application-tail-simulation V~V′
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
            (open-interpreter-narrowing-world-weaken R≤S M-terms))
          apply-simulation)
      (λ U V {n} {o} terminal eq k →
        application-tail-stable
          {W = U} {γ = γ} {θ = θ} {M = M} {V = V}
          {n = n} {o = o} terminal eq k)
      (λ U′ V′ {n} {o} terminal eq k →
        application-tail-stable
          {W = U′} {γ = γ′} {θ = θ′} {M = M′} {V = V′}
          {n = n} {o = o} terminal eq k)
      (λ { {n} eq →
        outcome-typing-excludes-error
          (target-interpret-typing environment terms n)
          (trans (application-computation-eq n) eq)
        }))
