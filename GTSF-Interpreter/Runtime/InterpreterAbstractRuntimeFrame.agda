module Runtime.InterpreterAbstractRuntimeFrame where

-- File Charter:
--   * Exposes the exact source-only runtime below an abstract type binder.
--   * Lifts static stores and realizes the fresh abstract source name without
--     allocating either runtime world.
--   * Lifts the synchronized term-environment realization into that runtime.
--   * Delegates the structural construction to a reduction-free proof module.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ)
open import Interpreter
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterAbstractRuntimeFrameProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-abstract-runtime :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ X}
    {R : WorldRelation W W′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  NTI.LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑ →
  RuntimeNarrowing R
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (suc Δᴸ) Δᴿ ρ↑
    (abstract-name X ∷ θ) θ′
left-abstract-runtime =
  Proof.left-abstract-runtime

left-abstract-environment-realization :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑ γ γ′ X}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing R
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (abstract-name X ∷ θ) θ′} →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  EnvironmentRealization runtime γᵀ γ γ′ →
  EnvironmentRealization runtime↑ γᵀ↑ γ γ′
left-abstract-environment-realization =
  Proof.left-abstract-environment-realization
