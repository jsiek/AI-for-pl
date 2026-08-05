module Runtime.InterpreterInstantiationRuntime where

-- File Charter:
--   * Public runtime-extension theorems for paired and source-only `ν`.
--   * Returns the exact related allocation worlds, shifted static stores,
--     and seal-prefixed runtime type environments used by instantiation.
--   * Delegates structural realization proofs to a reduction-free module.

open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing; type-narrowing)
open import Typing.InterpreterSemanticTypingCore using (WorldTyping)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterWorldNarrowing using (TypeEnvironmentScoped)
import NuTermImprecision as NTI
import proof.InterpreterInstantiationRuntimeProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-instantiation-runtime :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ A A′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  WorldTyping U →
  WorldTyping U′ →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (p⇑ :
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
      ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  NTI.LiftStoreⁱ
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Σ[ θ~θ′ ∈ TypeEnvironmentNarrowing S θ θ′ ]
    RuntimeNarrowing
      (allocate-both S (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName U) ∷ θ)
      (seal-name (freshSealName U′) ∷ θ′)
paired-instantiation-runtime =
  Proof.paired-instantiation-runtime

left-instantiation-runtime :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ A}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  WorldTyping U →
  WorldTyping U′ →
  WfTy Δᴸ A →
  (hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  NTI.LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Σ[ θ-ok ∈ TypeEnvironmentScoped U θ ]
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} S θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName U) ∷ θ) θ′
left-instantiation-runtime =
  Proof.left-instantiation-runtime
