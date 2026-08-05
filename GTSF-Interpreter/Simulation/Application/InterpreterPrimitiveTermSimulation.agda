module Simulation.Application.InterpreterPrimitiveTermSimulation where

-- File Charter:
--   * Public compositional simulation theorem for primitive terms.
--   * Takes the two recursive operand simulations through the general
--     open-term simulation motive.
--   * Delegates sequencing and world-transport details to its proof module.

open import ImprecisionWf using (idι)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTermNarrowingInversion
open import Simulation.Core.InterpreterTermSimulationMotive
open import Narrowing.InterpreterTypedValueNarrowing
import NuTerms as N
open import Primitives using (addℕ)
import proof.InterpreterPrimitiveTermSimulationCases as Proof
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

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
primitive-term-simulation =
  Proof.primitive-term-simulation
