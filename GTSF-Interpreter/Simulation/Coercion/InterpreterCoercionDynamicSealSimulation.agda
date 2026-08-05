module Simulation.Coercion.InterpreterCoercionDynamicSealSimulation where

-- File Charter:
--   * EXPERIMENTAL Milestone 5 typed simulations for source-only dynamic seal
--     and unseal; this module is currently blocked by O34.
--   * Connects static `X ⊑ ★` assumptions to runtime allocation provenance.
--   * Its left side may be suspended below a type abstraction and therefore
--     may contain abstract names; it must not yet be treated as an executable
--     all-seal runtime environment.
--   * Delegates computation and inversion details to a private proof module.

open import Coercions renaming
  (seal to sealᶜ; unseal to unsealᶜ)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing
import NuTermImprecision as NTI
open import Types
import proof.InterpreterCoercionDynamicSealSimulationProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-dynamic-seal-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A X μ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ sealᶜ A X ∶ A =⇒ ＇ X →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ) →
  TypedValueNarrowing
    ⟦ A ⟧[ θ ] ⟦ ★ ⟧[ θ′ ] R V V′ →
  TerminalSimulation
    (TypedValueResult ⟦ ＇ X ⟧[ θ ] ⟦ ★ ⟧[ θ′ ])
    R
    (coerceValue W θ (sealᶜ A X) V)
    (immediateReturn W′ V′)
left-dynamic-seal-coercion-simulation =
  Proof.left-dynamic-seal-coercion-simulation

left-dynamic-unseal-coercion-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ A X μ V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  μ ∣ Δᴸ ∣ NTI.leftStoreⁱ ρ
    ⊢ unsealᶜ X A ∶ ＇ X =⇒ A →
  (p : Φ ∣ Δᴸ ⊢ ＇ X ⊑ ★ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ ★ ⊣ Δᴿ) →
  TypedValueNarrowing
    ⟦ ＇ X ⟧[ θ ] ⟦ ★ ⟧[ θ′ ] R V V′ →
  TerminalSimulation
    (TypedValueResult ⟦ A ⟧[ θ ] ⟦ ★ ⟧[ θ′ ])
    R
    (coerceValue W θ (unsealᶜ X A) V)
    (immediateReturn W′ V′)
left-dynamic-unseal-coercion-simulation =
  Proof.left-dynamic-unseal-coercion-simulation
