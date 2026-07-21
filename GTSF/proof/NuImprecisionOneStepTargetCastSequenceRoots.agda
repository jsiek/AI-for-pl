module proof.NuImprecisionOneStepTargetCastSequenceRoots where

-- File Charter:
--   * Proves target-side beta-sequence root outcomes for ordinary narrowing
--     and widening casts.
--   * Takes explicit midpoint imprecision evidence rather than deriving it
--     from global right-context compatibility.
--   * Rebuilds the reduct relation with two nested target-cast constructors.
--   * Excludes dispatcher, store-well-formedness, and simulation-core
--     dependencies.

open import Data.List using ([])
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuReduction using (keep)
open import NuTermImprecision using (StoreImp; rightStoreⁱ)
open import NuTerms using (Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  )
open import TermTyping using (CastMode; SealModeStore★)
open import proof.NuImprecisionOneStepRelated using
  (weak-one-step-indexed-outcome-relatedᵀ)
open import proof.NuImprecisionSimulationResultDef using
  (WeakOneStepIndexedOutcome)


weak-one-step-target-narrow-cast-sequence-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A A′ C′ B′ s t μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ A′ ⊒ C′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C′ ⊒ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ A ⊑ C′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V ⟨ s ⟩ ⟨ t ⟩} {χ = keep} {ρ = ρ} q
weak-one-step-target-narrow-cast-sequence-root-outcomeᵀ
    mode seal★ s⊒ t⊒ M⊑V r q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (⊑cast⊒ᵀ mode seal★ t⊒
      (⊑cast⊒ᵀ mode seal★ s⊒ M⊑V r) q)


weak-one-step-target-widen-cast-sequence-root-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M V A A′ C′ B′ s t μ′}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ A′ ⊑ C′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C′ ⊑ B′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ V ⦂ A ⊑ A′ ∶ p →
  (r : Φ ∣ Δᴸ ⊢ A ⊑ C′ ⊣ Δᴿ) →
  (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Value V →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = V ⟨ s ⟩ ⟨ t ⟩} {χ = keep} {ρ = ρ} q
weak-one-step-target-widen-cast-sequence-root-outcomeᵀ
    mode seal★ s⊑ t⊑ M⊑V r q vV =
  weak-one-step-indexed-outcome-relatedᵀ
    (⊑cast⊑ᵀ mode seal★ t⊑
      (⊑cast⊑ᵀ mode seal★ s⊑ M⊑V r) q)
