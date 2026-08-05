module Simulation.Framed.InterpreterFramedEnvironmentLift where

-- File Charter:
--   * Exposes exact environment reindexing below paired and source-only
--     polymorphic binders and allocations.
--   * States the proof-relevant static contexts and runtime frames directly.
--   * Delegates the structural proof to a reduction-free private module.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using (_ˣ⊑★; ⇑ᴸᵢ)
open import Interpreter
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterFramedEnvironmentLiftProof as Proof
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-framed-environment-lift :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑}
    {γ γ′ α α′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing S (∀ᵢᶜ Φ)
        (suc Δᴸ) (suc Δᴿ) ρ↑
        (seal-name α ∷ θ) (seal-name α′ ∷ θ′)} →
  AssumptionMembershipUnique Φ →
  RelatedWorlds.WorldExtension R S →
  NTI.LiftCtxⁱ (∀ᵢᶜ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
paired-framed-environment-lift =
  Proof.paired-framed-environment-lift

left-framed-environment-lift :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑}
    {γ γ′ α}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing S
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (seal-name α ∷ θ) θ′} →
  AssumptionMembershipUnique Φ →
  RelatedWorlds.WorldExtension R S →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
left-framed-environment-lift =
  Proof.left-framed-environment-lift

left-abstract-framed-environment-lift :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ ρ↑ θ θ′ γᵀ γᵀ↑ γ γ′ X}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′}
    {runtime↑ :
      RuntimeNarrowing R
        ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        (suc Δᴸ) Δᴿ ρ↑
        (abstract-name X ∷ θ) θ′} →
  AssumptionMembershipUnique Φ →
  NTI.LiftLeftCtxⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑ →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  FramedEnvironmentNarrowing runtime↑ γᵀ↑ γ γ′
left-abstract-framed-environment-lift =
  Proof.left-abstract-framed-environment-lift
