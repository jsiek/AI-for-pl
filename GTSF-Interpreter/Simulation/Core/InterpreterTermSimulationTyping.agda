module Simulation.Core.InterpreterTermSimulationTyping where

-- File Charter:
--   * EXPERIMENTAL (O34): source typing is available only with an explicit
--     executable-runtime certificate; suspended abstract bodies need a
--     distinct typing phase before this can rejoin the full simulation.
--   * Public typing upgrade for direct open-term simulation.
--   * Makes the typed returned-value relation explicit in the theorem.
--   * Delegates unary typing assembly to the proof module.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore using
  (OutcomeTyping; ⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
import proof.InterpreterTermSimulationTypingProof as Proof
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

source-interpret-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  RuntimeTypeEnvironment θ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  ∀ n →
  OutcomeTyping W ⟦ A ⟧[ θ ] (interpret W γ θ N n)
source-interpret-typing =
  Proof.source-interpret-typing

target-interpret-typing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  ∀ n →
  OutcomeTyping W′ ⟦ B ⟧[ θ′ ] (interpret W′ γ′ θ′ N′ n)
target-interpret-typing =
  Proof.target-interpret-typing

term-typed-result-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′ A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  RuntimeTypeEnvironment θ →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′) →
  TerminalSimulation
    (TypedValueResult ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ])
    R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
term-typed-result-simulation =
  Proof.term-typed-result-simulation
