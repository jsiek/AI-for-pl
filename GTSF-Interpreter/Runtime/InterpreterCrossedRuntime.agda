module Runtime.InterpreterCrossedRuntime where

-- File Charter:
--   * Public crossed-runtime theorem for adjacent universal exchange.
--   * States the two sibling dynamic allocations, swapped static context,
--     crossed store links, and final type-name environments explicitly.
--   * Delegates the reduction-free construction to a private proof module.

open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)

open import ImprecisionWf using
  (_ˣ⊑ˣ_; ⇑ᵢ; swapRight∀∀ᵢ; id★)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using (type-narrowing)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization using
  (environments-narrow)
import NuTermImprecision as NTI
import proof.InterpreterCrossedRuntimeProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


crossed-dynamic-runtime :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ₀ ρ₁ ρ₂ θ θ′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ₀ θ θ′) →
  NTI.LiftStoreⁱ
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
  NTI.LiftStoreⁱ
    (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RuntimeNarrowing
    (allocate-crossed
      {A₀ = ★} {A₁ = ★} {B₀ = ★} {B₁ = ★}
      {θA₀ = θ} {θA₁ = θ} {θB₀ = θ′} {θB₁ = θ′} R
      (type-narrowing
        {Φ = []} {Δᴸ = zero} {Δᴿ = zero} id★)
      (environments-narrow
        (type-environments-realized runtime))
      (type-narrowing
        {Φ = []} {Δᴸ = zero} {Δᴿ = zero} id★)
      (environments-narrow
        (type-environments-realized runtime)))
    (swapRight∀∀ᵢ Φ)
    (suc (suc Δᴸ)) (suc (suc Δᴿ))
    (NTI.crossedStoreⁱ wf★ wf★ wf★ wf★
      id★ id★ ρ₂)
    (seal-name (freshSealName (allocate W ★ θ)) ∷
      seal-name (freshSealName W) ∷ θ)
    (seal-name (freshSealName (allocate W′ ★ θ′)) ∷
      seal-name (freshSealName W′) ∷ θ′)
crossed-dynamic-runtime =
  Proof.crossed-dynamic-runtime
