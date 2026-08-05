module Simulation.Application.InterpreterApplicationSimulation where

-- File Charter:
--   * Public compositional simulation theorem for term application.
--   * Takes recursive function, argument, and semantic-application
--     simulations explicitly for use by the later mutual driver.
--   * Delegates asynchronous sequencing to its focused proof module.

open import ImprecisionWf using
  (_↦_; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Application.InterpreterApplicationSimulationMotive
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Simulation.Core.InterpreterTermSimulationMotive
open import Narrowing.InterpreterTypedValueNarrowing
import NuTerms as N
import proof.InterpreterApplicationSimulationCases as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

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
application-term-simulation =
  Proof.application-term-simulation
