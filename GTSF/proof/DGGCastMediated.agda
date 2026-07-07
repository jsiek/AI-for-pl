{-# OPTIONS --allow-unsolved-metas #-}

module proof.DGGCastMediated where

-- File Charter:
--   * Mediated-store DGG helpers for target-side cast steps.
--   * Packages direct cast simulations whose proof should stay out of the
--     main DynamicGradualGuaranteeMediated case split.
--   * Currently exports the target `β-id` cases for `⊒cast+ᵗ` and
--     `⊒cast-ᵗ`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  ; applyRightChange
  )

------------------------------------------------------------------------
-- Endpoint transport
------------------------------------------------------------------------

typed-term-narrowing-endpointsᵐᶜ :
  ∀ {ΔL ΔR ρ γ M M′ p A B A′ B′} →
  A ≡ A′ →
  B ≡ B′ →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ B →
  ΔL ∣ ΔR ∣ ρ ∣ γ ⊢ M ⊒ M′ ∶ p ⦂ A′ ⊒ᵐ B′
typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′ = M⊒M′

------------------------------------------------------------------------
-- Direct target cast simulation
------------------------------------------------------------------------

target-cast-plus-β-idᵐ :
  ∀ {ΔL ΔR ρ M M′ p r A B C T η} →
  η ∣ ΔR ∣ rightStore ρ ⊢ id T ∶ C ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ r ⦂ A ⊒ᵐ B →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep C) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ M′ ∶ r′ ⦂ C′ ⊒ᵐ D′
target-cast-plus-β-idᵐ (cast-id _ _ , _) M⊒M′ =
  [] ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′

target-cast-minus-β-idᵐ :
  ∀ {ΔL ΔR ρ M M′ p r A B C T η} →
  η ∣ ΔR ∣ rightStore ρ ⊢ id T ∶ C ⊒ B →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ᵐ C →
  ∃[ χs ] ∃[ N ] ∃[ ΔL′ ] ∃[ ΔR′ ] ∃[ ρ′ ]
  ∃[ C′ ] ∃[ D′ ] ∃[ r′ ]
    (M —↠[ χs ] N) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    (ΔR′ ≡ applyTyCtx keep ΔR) ×
    (ρ′ ≡ applyRightChange keep (applyLeftChanges χs ρ)) ×
    (C′ ≡ applyTys χs A) ×
    (D′ ≡ applyTy keep B) ×
    ΔL′ ∣ ΔR′ ∣ ρ′ ∣ []
      ⊢ N ⊒ M′ ∶ r′ ⦂ C′ ⊒ᵐ D′
target-cast-minus-β-idᵐ (cast-id _ _ , _) M⊒M′ =
  [] ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  _ ,
  ↠-refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  refl ,
  typed-term-narrowing-endpointsᵐᶜ refl refl M⊒M′
