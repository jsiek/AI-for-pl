module proof.NuImprecisionOneStepSourceCastFrames where

-- File Charter:
--   * Freezes the two outcome-level source-cast frames needed by the indexed
--     one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome, so the
--     recursive dispatcher clauses need only one further lemma application.
--   * The related branches are backed by the checked narrow/widen indexed
--     result frames; source blame is lifted by the checked cast-blame tail.
--   * Contains exactly the two intended leaf-proof wrappers.

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (_⟨_⟩)
open import TermTyping using (CastMode; SealModeStore★)
open import proof.NuImprecisionSimulation using
  ( weak-one-step-source-narrow-cast-indexed-frameᵀ
  ; weak-one-step-source-widen-cast-indexed-frameᵀ
  )
open import proof.NuImprecisionSimulationCore using
  ( WeakOneStepIndexedOutcome
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  ; transportAllCoherent
  ; transportArrowCoherent
  ; transportNo•Terms
  ; weak-step-transport
  ; weak-step-type-coherence
  )
open import proof.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊒
    (indexed-outcome-related indexed transport coherence) =
  indexed-outcome-related
    (weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★ c⊒ indexed)
    (weak-step-transport (transportNo•Terms transport))
    (weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence))
weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊒
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)


weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊑
    (indexed-outcome-related indexed transport coherence) =
  indexed-outcome-related
    (weak-one-step-source-widen-cast-indexed-frameᵀ
      mode seal★ c⊑ indexed)
    (weak-step-transport (transportNo•Terms transport))
    (weak-step-type-coherence
      (transportArrowCoherent coherence)
      (transportAllCoherent coherence))
weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊑
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
