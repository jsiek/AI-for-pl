module proof.NuDGGTerminalBackwardValueIntegration where

-- File Charter:
--   * Checks that the live target-step dispatcher and terminal value catch-up
--     have exactly the interfaces required by backward value trace assembly.
--   * This is an integration-batch target and imports partial leaf modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  ; _—↠[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; Value; blame)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; prefix-reflⁱ
  )
open import proof.NuDGGTerminalBackwardValueAssembly using
  (backward-target-value-or-source-blame-general-from-componentsᵀ)
open import proof.NuImprecisionCatchupScratch using
  ( left-catchup-indexed-prefixᵀ
  ; weak-one-step-indexed-simulationᵀ
  )


backward-target-value-or-source-blame-general-integratedᵀ :
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ V′ χs′ →
  M′ —↠[ χs′ ] V′ →
  Value V′ →
    (∃[ V ] (Σ[ χs ∈ StoreChanges ]
    (∃[ Ψ ] (Σ[ ρ′ ∈
        StoreImp Ψ
          (applyTyCtxs χs Δᴸ) (applyTyCtxs χs′ Δᴿ) ]
    (Σ[ q ∈
        (Ψ ∣ applyTyCtxs χs Δᴸ
          ⊢ applyTys χs A ⊑ applyTys χs′ B
          ⊣ applyTyCtxs χs′ Δᴿ) ]
      ((M —↠[ χs ] V) ×
       Value V ×
       (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
       (rightStoreⁱ ρ′ ≡ applyStores χs′ (rightStoreⁱ ρ)) ×
       Ψ ∣ applyTyCtxs χs Δᴸ
         ∣ applyTyCtxs χs′ Δᴿ ∣ ρ′ ∣ []
         ⊢ᴺ V ⊑ V′
         ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
    ⊎ (∃[ χs ] (M —↠[ χs ] blame)))
backward-target-value-or-source-blame-general-integratedᵀ =
  backward-target-value-or-source-blame-general-from-componentsᵀ
    weak-one-step-indexed-simulationᵀ
    (λ okM vV′ noV′ M⊑V′ →
      left-catchup-indexed-prefixᵀ
        prefix-reflⁱ okM vV′ noV′ M⊑V′)
