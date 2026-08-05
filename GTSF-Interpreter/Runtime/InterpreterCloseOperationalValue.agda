module Runtime.InterpreterCloseOperationalValue where

-- File Charter:
--   * Exposes the reduction-free close-value theorem with exact operational
--     producer origins.
--   * Keeps the public statement explicit while delegating its proof to the
--     private structural induction.

open import Interpreter
open import Runtime.InterpreterClosedValue
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTerms as N
open import Types
import proof.InterpreterCloseOperationalValueProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

close-aligned-operational :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′}
    {vM : N.Value M} {vM′ : N.Value M′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p) →
  (runtime :
    RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment :
    EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  ClosedValue γ θ vM U →
  ClosedValue γ′ θ′ vM′ U′ →
  OperationalValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ] R U U′
close-aligned-operational =
  Proof.close-aligned-operational
