module Simulation.Core.InterpreterTermSimulationSimple where

-- File Charter:
--   * Public variable, closure, and constant cases for direct term simulation.
--   * States each theorem against the concrete synchronized runtime context.
--   * Delegates proof scripts to the focused simple-case module.

open import Interpreter
open import Data.List using (_∷_)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import Primitives using (Const)
import proof.InterpreterTermSimulationSimpleCases as Proof
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

variable-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ x A B p}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  γᵀ ∋ x ⦂ NTI.ctx-imp A B p →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.` x))
    (interpret W′ γ′ θ′ (N.` x))
variable-simulation =
  Proof.variable-simulation

closure-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ θ θ′ γ γ′ N N′}
    {A A′ B B′ pA pB}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  EnvironmentRealization runtime γᵀ γ γ′ →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ (NTI.ctx-imp A A′ pA ∷ γᵀ)
    N N′ B B′ pB →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.ƛ N))
    (interpret W′ γ′ θ′ (N.ƛ N′))
closure-simulation =
  Proof.closure-simulation

constant-simulation :
  ∀ {W W′ γ γ′ θ θ′}
    {R : WorldRelation W W′} →
  (κ : Const) →
  TerminalSimulation ValueNarrowing R
    (interpret W γ θ (N.$ κ))
    (interpret W′ γ′ θ′ (N.$ κ))
constant-simulation =
  Proof.constant-simulation
