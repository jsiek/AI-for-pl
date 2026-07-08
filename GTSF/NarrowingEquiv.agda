module NarrowingEquiv where

-- File Charter:
--   * Defines the two-namespace analogue of the paper's `r ≈_σ r′`
--     relation for narrowing indices.
--   * The left narrowing is typed in the left store projected from `σ`,
--     the right narrowing is typed in the right store projected from `σ`,
--     and the source/target endpoint pairs are related by `MedTy`.
--   * This module only packages the relation; transport and inversion
--     lemmas should live in proof modules.

open import Types
open import Coercions
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import Mediation using (MedTy)
open import StoreNarrowing

------------------------------------------------------------------------
-- Store-indexed equivalence of narrowing evidence
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢_≈_∶_⊒_⦂_⊒_

data _∣_∣_∣_∣_⊢_≈_∶_⊒_⦂_⊒_ :
    ModeEnv → ModeEnv → TyCtx → TyCtx → StoreNarrowingCtx →
    Coercion → Coercion → Ty → Ty → Ty → Ty → Set₁ where

  endpointsⁿ : ∀ {μL μR ΔL ΔR σ r r′ A B A′ B′} →
    MedTy (StoreMatchedVar σ) A A′ →
    MedTy (StoreMatchedVar σ) B B′ →
    μL ∣ ΔL ∣ leftStore σ ⊢ r ∶ A ⊒ B →
    μR ∣ ΔR ∣ rightStore σ ⊢ r′ ∶ A′ ⊒ B′ →
      ------------------------------------------------------
    μL ∣ μR ∣ ΔL ∣ ΔR ∣ σ ⊢ r ≈ r′ ∶ A ⊒ B ⦂ A′ ⊒ B′

≈-left-typing :
  ∀ {μL μR ΔL ΔR σ r r′ A B A′ B′} →
  μL ∣ μR ∣ ΔL ∣ ΔR ∣ σ ⊢ r ≈ r′ ∶ A ⊒ B ⦂ A′ ⊒ B′ →
  μL ∣ ΔL ∣ leftStore σ ⊢ r ∶ A ⊒ B
≈-left-typing (endpointsⁿ medA medB r⊒ r′⊒) = r⊒

≈-right-typing :
  ∀ {μL μR ΔL ΔR σ r r′ A B A′ B′} →
  μL ∣ μR ∣ ΔL ∣ ΔR ∣ σ ⊢ r ≈ r′ ∶ A ⊒ B ⦂ A′ ⊒ B′ →
  μR ∣ ΔR ∣ rightStore σ ⊢ r′ ∶ A′ ⊒ B′
≈-right-typing (endpointsⁿ medA medB r⊒ r′⊒) = r′⊒
