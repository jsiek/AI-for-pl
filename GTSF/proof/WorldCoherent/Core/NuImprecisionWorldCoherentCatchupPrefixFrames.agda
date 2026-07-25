module proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames where

-- File Charter:
--   * Lifts target cast frames over world-coherent catch-up results.
--   * Records that target-only framing preserves the final world and left
--     store well-formedness by construction.
--   * Contains no recursive catch-up dispatcher or semantic leaf proof.

open import Coercions using (id-onlyᵈ)
open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Conversion using (ConcealConversion; RevealConversion)
open import ConversionIndexCompatibility using (_[_↦_]ᴿ_)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
open import proof.Catchup.Core.NuImprecisionCatchupPrefixSupport
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef


world-coherent-left-catchup-prefix-target-narrow-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊒ B′ →
  narrowing ⊢ᶜ c ⦂ s →
  ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒ c-shape comp
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-narrow-castᵀ
      prefix mode seal★ c⊒ c-shape comp catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique wfL

world-coherent-left-catchup-prefix-target-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  p [ β ↦ X′ ]ᴿ q →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-reveal-castᵀ
    prefix c↑ replace
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-reveal-castᵀ
      prefix c↑ replace catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique wfL

world-coherent-left-catchup-prefix-target-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  q [ β ↦ X′ ]ᴿ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-conceal-castᵀ
    prefix c↓ replace
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-conceal-castᵀ
      prefix c↓ replace catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique wfL

world-coherent-left-catchup-prefix-target-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′ →
  widening ⊢ᶜ c ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑ c-shape comp
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-widen-castᵀ
      prefix mode seal★ c⊑ c-shape comp catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique wfL

world-coherent-left-catchup-prefix-target-widen-id-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c s}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′ →
  widening ⊢ᶜ c ⦂ s →
  ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-widen-id-castᵀ
    prefix seal★ c⊑ c-shape comp
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final))
      lineage coherent exclusive unique wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-widen-id-castᵀ
      prefix seal★ c⊑ c-shape comp catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive unique wfL
