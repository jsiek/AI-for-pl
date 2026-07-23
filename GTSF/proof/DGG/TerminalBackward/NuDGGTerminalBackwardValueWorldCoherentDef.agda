module proof.DGG.TerminalBackward.NuDGGTerminalBackwardValueWorldCoherentDef where

-- File Charter:
--   * Defines the arbitrary-world backward target-value-or-source-blame
--     contract with the world/store-name coherence premise required by
--     target seal cancellation.
--   * Carries source-name role exclusivity required by source seal
--     cancellation through arbitrary-world recursion.
--   * Keeps the complete terminal alternatives explicit at the use site.
--   * Contains no implementation and imports only statement-level support.

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
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)


WorldCoherentBackwardTargetValueOrSourceBlameᵀ : Set₁
WorldCoherentBackwardTargetValueOrSourceBlameᵀ =
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
