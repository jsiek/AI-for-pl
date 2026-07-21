module proof.NuImprecisionWorldCoherentCatchupPrefixFrames where

-- File Charter:
--   * Lifts target cast frames over world-coherent catch-up results.
--   * Records that target-only framing preserves the final world and left
--     store well-formedness by construction.
--   * Contains no recursive catch-up dispatcher or semantic leaf proof.

open import Coercions using (id-onlyᵈ)
open import Agda.Builtin.Equality using (refl)
open import Conversion using (ConcealConversion; RevealConversion)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_; _∣_∣_⊢_∶_⊒_)
open import NuTermImprecision using
  (StoreImp; rightStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
open import proof.NuImprecisionCatchupPrefixSupport
open import proof.NuImprecisionSimulationResultDef
open import proof.NuImprecisionWeakOneStepStoreLineageDef
open import proof.NuImprecisionWorldCoherentResultDef


world-coherent-left-catchup-prefix-target-narrow-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊒ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        transport type-coherence)
      lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-narrow-castᵀ
      prefix mode seal★ c⊒ catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive wfL

world-coherent-left-catchup-prefix-target-reveal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RevealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-reveal-castᵀ
    prefix c↑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        transport type-coherence)
      lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-reveal-castᵀ
      prefix c↑ catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive wfL

world-coherent-left-catchup-prefix-target-conceal-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ β X′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ConcealConversion μ Δᴿ (rightStoreⁱ ρ₀)
    β X′ c A′ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-conceal-castᵀ
    prefix c↓
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        transport type-coherence)
      lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-conceal-castᵀ
      prefix c↓ catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive wfL

world-coherent-left-catchup-prefix-target-widen-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c μ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ μ (rightStoreⁱ ρ₀) →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        transport type-coherence)
      lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-widen-castᵀ
      prefix mode seal★ c⊑ catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive wfL

world-coherent-left-catchup-prefix-target-widen-id-castᵀ :
  ∀ {Φ Δᴸ Δᴿ M V′ A A′ B′ c}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
  id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ A′ ⊑ B′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′} {ρ = ρ⁺} p →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = V′ ⟨ c ⟩} {ρ = ρ⁺} q
world-coherent-left-catchup-prefix-target-widen-id-castᵀ
    prefix seal★ c⊑
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        (left-catchup-invariant
          (left-silent-invariant refl refl) final)
        transport type-coherence)
      lineage coherent exclusive wfL) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-target-widen-id-castᵀ
      prefix seal★ c⊑ catchup)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    coherent exclusive wfL
