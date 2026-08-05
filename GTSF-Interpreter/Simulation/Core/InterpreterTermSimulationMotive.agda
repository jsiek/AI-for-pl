module Simulation.Core.InterpreterTermSimulationMotive where

-- File Charter:
--   * Defines the reusable open-term motive for constructive interpreter
--     simulation.
--   * Quantifies over every synchronized runtime realization so recursive
--     calls remain valid after related-world extension.
--   * Carries semantic typing in the returned-value relation.

open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
import NuTermImprecision as NTI
import NuTerms as N
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

InterpreterTermSimulation :
  (Φ : ImpCtx) →
  (Δᴸ Δᴿ : TyCtx) →
  (ρ : NTI.StoreImp Φ Δᴸ Δᴿ) →
  (γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ) →
  (N N′ : N.Term) →
  (A B : Ty) →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
  Set₂
InterpreterTermSimulation Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p =
  ∀ {W W′ θ θ′ γ γ′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (terms :
    OpenInterpreterTermNarrowing
      R Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  TerminalSimulation
    (TypedValueResult ⟦ A ⟧[ θ ] ⟦ B ⟧[ θ′ ])
    R
    (interpret W γ θ N)
    (interpret W′ γ′ θ′ N′)
