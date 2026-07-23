module proof.DGG.TerminalBackward.NuDGGTerminalBackwardBlameIntegration where

-- File Charter:
--   * Checks that the live target-step dispatcher and target-blame catch-up
--     have exactly the interfaces required by backward terminal trace
--     assembly.
--   * This is an integration-batch check target; cheap terminal-statement
--     checks deliberately do not import the large dispatcher scratch module.

open import Data.List using ([])
open import Data.Product using (∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—↠[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.DGG.TerminalBackward.NuDGGTerminalBackwardBlameAssembly using
  (backward-target-blame-general-from-componentsᵀ)
open import proof.Catchup.Core.NuImprecisionCatchupScratch using
  (weak-one-step-indexed-simulationᵀ)
open import proof.Target.Core.NuImprecisionTargetBlameCatchup using
  (left-catchup-target-blameᵀ)


backward-target-blame-general-integratedᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  M′ —↠[ χs′ ] blame →
  ∃[ χs ] (M —↠[ χs ] blame)
backward-target-blame-general-integratedᵀ =
  backward-target-blame-general-from-componentsᵀ
    weak-one-step-indexed-simulationᵀ
    left-catchup-target-blameᵀ
