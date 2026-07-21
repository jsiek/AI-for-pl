module proof.NuDGGTerminalForwardDef where

-- File Charter:
--   * Defines the arbitrary-world forward source-value terminal contract.
--   * Carries world coherence and source-name exclusivity through the recursive
--     source trace while keeping the final DGG package fully explicit.
--   * Contains no implementation and imports only statement-level support.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)

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
open import NuTerms using (RuntimeOK; Value)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)


WorldCoherentForwardSourceValueᵀ : Set₁
WorldCoherentForwardSourceValueᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ V χs →
  M —↠[ χs ] V →
  Value V →
  ∃[ V′ ] (Σ[ θs ∈ StoreChanges ]
  (∃[ Ψ ] (Σ[ ρ′ ∈
      StoreImp Ψ
        (applyTyCtxs χs Δᴸ) (applyTyCtxs θs Δᴿ) ]
  (Σ[ q ∈
      (Ψ ∣ applyTyCtxs χs Δᴸ
        ⊢ applyTys χs A ⊑ applyTys θs B
        ⊣ applyTyCtxs θs Δᴿ) ]
    ((M′ —↠[ θs ] V′) ×
     Value V′ ×
     (leftStoreⁱ ρ′ ≡ applyStores χs (leftStoreⁱ ρ)) ×
     (rightStoreⁱ ρ′ ≡ applyStores θs (rightStoreⁱ ρ)) ×
     Ψ ∣ applyTyCtxs χs Δᴸ
       ∣ applyTyCtxs θs Δᴿ ∣ ρ′ ∣ []
       ⊢ᴺ V ⊑ V′
       ⦂ applyTys χs A ⊑ applyTys θs B ∶ q)))))
