module Simulation.Framed.InterpreterFramedEnvironmentLookup where

-- File Charter:
--   * Exposes exact lookup in a runtime-framed term environment.
--   * Preserves the static precision derivation at the selected entry.
--   * Delegates exhaustive context recursion to a private proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedEnvironmentLookupProof as Proof
open import Types

framed-environment-lookup :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ γᵀ γ γ′ x A A′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {R : RelatedWorlds.WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  γᵀ ∋ x ⦂ NTI.ctx-imp A A′ p →
  Σ[ V ∈ Value ]
  Σ[ V′ ∈ Value ]
    lookup γ x ≡ just V ×
    lookup γ′ x ≡ just V′ ×
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = p} runtime V V′
framed-environment-lookup =
  Proof.framed-environment-lookup
