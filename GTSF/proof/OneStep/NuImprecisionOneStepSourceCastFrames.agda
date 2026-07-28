module proof.OneStep.NuImprecisionOneStepSourceCastFrames where

-- File Charter:
--   * Freezes the two outcome-level source-cast frames needed by the indexed
--     one-step dispatcher.
--   * Each wrapper consumes an already-computed inner indexed outcome, so the
--     recursive dispatcher clauses need only one further lemma application.
--   * The related branches are backed by the checked narrow/widen indexed
--     result frames; source blame is lifted by the checked cast-blame tail.
--   * Contains exactly the two intended leaf-proof wrappers.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (widening)
open import ImprecisionComposition using (⌊_⌋; _；_≋_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (_⟨_⟩)
open import TermTyping using (CastMode; SealModeStore★)
open import proof.Catchup.Simulation.NuImprecisionSimulation using
  ( weak-one-step-source-narrow-cast-indexed-frameᵀ
  ; weak-one-step-source-widen-cast-indexed-frameᵀ
  )
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepIndexedOutcome
  ; indexed-outcome-related
  ; indexed-outcome-source-blame
  )
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (cast-blame-tailᵀ)


weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊒ B →
  CastShape.narrowing ⊢ᶜ c ⦂ s →
  s ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊒ c-shape comp
    (indexed-outcome-related indexed) =
  indexed-outcome-related
    (weak-one-step-source-narrow-cast-indexed-frameᵀ
      mode seal★ c⊒ c-shape comp indexed)
weak-one-step-source-narrow-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊒ c-shape comp
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)


weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ :
  ∀ {Φ Δᴸ Δᴿ M N′ A A′ B c μ χ s}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ}
    {ρ : StoreImp Φ Δᴸ Δᴿ} →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastShape.widening ⊢ᶜ c ⦂ s →
  s ； ⌊ q ⌋ ≋ ⌊ p ⌋ →
  WeakOneStepIndexedOutcome
    {M = M} {N′ = N′} {χ = χ} {ρ = ρ} p →
  WeakOneStepIndexedOutcome
    {M = M ⟨ c ⟩} {N′ = N′} {χ = χ} {ρ = ρ} q
weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊑ c-shape comp
    (indexed-outcome-related indexed) =
  indexed-outcome-related
    (weak-one-step-source-widen-cast-indexed-frameᵀ
      mode seal★ c⊑ c-shape comp indexed)
weak-one-step-source-widen-cast-indexed-frame-outcomeᵀ
    mode seal★ c⊑ c-shape comp
    (indexed-outcome-source-blame source↠) =
  indexed-outcome-source-blame (cast-blame-tailᵀ source↠)
