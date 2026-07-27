module
  proof.Quotient.NuImprecisionTargetInstantiationTransportTerminalExperiment
  where

-- File Charter:
--   * Proves that exact and canonically transported target-instantiation
--     creation endpoints are values and therefore cannot take a leading step.
--   * Discharges the new source- and target-simulation cases introduced by
--     the creation-specific transported constructor.
--   * Imports no legacy term-imprecision judgment and contains no postulate,
--     hole, permissive option, termination bypass, or catch-all clause.

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Coercions using (Inert)
open import NuReduction using (_—→[_]_)
open import NuTerms using
  (Term; Value; Λ_; _⟨_⟩; renameᵗᵐ)
open import Types using (Renameᵗ)
open import proof.Core.Properties.NuTermProperties using
  (renameᵗᵐ-preserves-Value)
open import proof.DGG.Core.NuPreservation using (value-no-step)


target-instantiation-transport-valuesᴿ :
  ∀ {W W′ s} →
  (τ σ : Renameᵗ) →
  Value W →
  Value W′ →
  Inert s →
  Value (renameᵗᵐ τ (Λ W)) ×
  Value (renameᵗᵐ σ (W′ ⟨ s ⟩))
target-instantiation-transport-valuesᴿ τ σ vW vW′ inert =
  renameᵗᵐ-preserves-Value τ (Λ vW) ,
  renameᵗᵐ-preserves-Value σ (vW′ ⟨ inert ⟩)


target-instantiation-transport-source-no-stepᴿ :
  ∀ {W W′ s χ N} →
  (τ σ : Renameᵗ) →
  (vW : Value W) →
  (vW′ : Value W′) →
  (inert : Inert s) →
  renameᵗᵐ τ (Λ W) —→[ χ ] N →
  ⊥
target-instantiation-transport-source-no-stepᴿ
    τ σ vW vW′ inert source-step =
  value-no-step
    (proj₁
      (target-instantiation-transport-valuesᴿ
        τ σ vW vW′ inert))
    source-step


target-instantiation-transport-target-no-stepᴿ :
  ∀ {W W′ s χ N′} →
  (τ σ : Renameᵗ) →
  (vW : Value W) →
  (vW′ : Value W′) →
  (inert : Inert s) →
  renameᵗᵐ σ (W′ ⟨ s ⟩) —→[ χ ] N′ →
  ⊥
target-instantiation-transport-target-no-stepᴿ
    τ σ vW vW′ inert target-step =
  value-no-step
    (proj₂
      (target-instantiation-transport-valuesᴿ
        τ σ vW vW′ inert))
    target-step
