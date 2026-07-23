module BigStepDynamicGradualGuarantee where

-- File Charter:
--   * Big-step formulation of the closed gradual-term dynamic gradual
--     guarantee.
--   * Replaces terminal small-step traces by structural big-step derivations
--     while preserving allocation traces, final stores, types, and worlds.
--   * This is a checked statement surface; no proof is claimed here.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_)

open import BigStep
open import BigStepObservations
open import DynamicGradualGuarantee using
  (compiled-left; compiled-right)
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyStores
  ; applyTyCtxs
  ; applyTys
  )
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (Value; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types

BigStepGradualDGG : Set₁
BigStepGradualDGG =
  ∀ {M M′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  (M⊑M′ : [] ∣ 0 ∣ 0 ∣ [] ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
    -- If the left run returns a value, the right run returns a related value.
    (∀ V χs →
      compiled-left M⊑M′ ⇓[ χs ] V →
      Value V →
      ∃[ V′ ] (Σ[ χs′ ∈ StoreChanges ]
      (∃[ Φ ] (Σ[ ρ ∈
          StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
      (Σ[ q ∈
          (Φ ∣ applyTyCtxs χs 0
            ⊢ applyTys χs A ⊑ applyTys χs′ B
            ⊣ applyTyCtxs χs′ 0) ]
        ((compiled-right M⊑M′ ⇓[ χs′ ] V′) ×
         Value V′ ×
         (leftStoreⁱ ρ ≡ applyStores χs []) ×
         (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
         Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
           ⊢ᴺ V ⊑ V′
           ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q))))))
    -- If the left run diverges, the right run diverges.
    × (Divergesᵇ (compiled-left M⊑M′) →
       Divergesᵇ (compiled-right M⊑M′))
    -- A right value is matched by a related left value or by left blame.
    × (∀ V′ χs′ →
      compiled-right M⊑M′ ⇓[ χs′ ] V′ →
      Value V′ →
        (∃[ V ] (Σ[ χs ∈ StoreChanges ]
        (∃[ Φ ] (Σ[ ρ ∈
            StoreImp Φ (applyTyCtxs χs 0) (applyTyCtxs χs′ 0) ]
        (Σ[ q ∈
            (Φ ∣ applyTyCtxs χs 0
              ⊢ applyTys χs A ⊑ applyTys χs′ B
              ⊣ applyTyCtxs χs′ 0) ]
          ((compiled-left M⊑M′ ⇓[ χs ] V) ×
           Value V ×
           (leftStoreⁱ ρ ≡ applyStores χs []) ×
           (rightStoreⁱ ρ ≡ applyStores χs′ []) ×
           Φ ∣ applyTyCtxs χs 0 ∣ applyTyCtxs χs′ 0 ∣ ρ ∣ []
             ⊢ᴺ V ⊑ V′
             ⦂ applyTys χs A ⊑ applyTys χs′ B ∶ q)))))
        ⊎ (Σ[ χs ∈ StoreChanges ]
             (compiled-left M⊑M′ ⇓[ χs ] blame))))
    -- If the right run diverges, the left cannot return a value: on closed
    -- typed programs it therefore diverges or returns blame.
    × (Divergesᵇ (compiled-right M⊑M′) →
       DivergesOrBlamesᵇ (compiled-left M⊑M′))
