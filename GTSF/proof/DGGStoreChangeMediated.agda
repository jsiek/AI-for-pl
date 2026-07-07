module proof.DGGStoreChangeMediated where

-- File Charter:
--   * Store-change commutation lemmas used by the mediated DGG helper
--     modules.
--   * Keeps structural SealCorr equalities out of
--     proof.DynamicGradualGuaranteeMediated.
--   * Currently exposes the right-shift/left-change commutation needed
--     when an IH runs under a target-side allocation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import Types
open import NuReduction using (StoreChange; StoreChanges; keep; bind)
open import StoreCorrespondence
open import proof.CatchupSeparated using
  ( applyLeftChange
  ; applyLeftChanges
  )
open import proof.NarrowWidenProperties using
  ( StoreDetWf
  ; StoreDetWf-⟰ᵗ-inv
  )

⇑ˡᶜorr-⇑ʳᶜorr-commute :
  ∀ ρ → ⇑ˡᶜorr (⇑ʳᶜorr ρ) ≡ ⇑ʳᶜorr (⇑ˡᶜorr ρ)
⇑ˡᶜorr-⇑ʳᶜorr-commute [] = refl
⇑ˡᶜorr-⇑ʳᶜorr-commute (matched α A β B ∷ ρ) =
  cong (matched (suc α) (⇑ᵗ A) (suc β) (⇑ᵗ B) ∷_)
    (⇑ˡᶜorr-⇑ʳᶜorr-commute ρ)
⇑ˡᶜorr-⇑ʳᶜorr-commute (left-only α A ∷ ρ) =
  cong (left-only (suc α) (⇑ᵗ A) ∷_)
    (⇑ˡᶜorr-⇑ʳᶜorr-commute ρ)
⇑ˡᶜorr-⇑ʳᶜorr-commute (right-only β B ∷ ρ) =
  cong (right-only (suc β) (⇑ᵗ B) ∷_)
    (⇑ˡᶜorr-⇑ʳᶜorr-commute ρ)

applyLeftChange-⇑ʳᶜorr :
  ∀ χ ρ → applyLeftChange χ (⇑ʳᶜorr ρ) ≡ ⇑ʳᶜorr (applyLeftChange χ ρ)
applyLeftChange-⇑ʳᶜorr keep ρ = refl
applyLeftChange-⇑ʳᶜorr (bind A) ρ =
  cong (left-only zero (⇑ᵗ A) ∷_)
    (⇑ˡᶜorr-⇑ʳᶜorr-commute ρ)

applyLeftChanges-⇑ʳᶜorr :
  ∀ χs ρ →
  applyLeftChanges χs (⇑ʳᶜorr ρ) ≡
    ⇑ʳᶜorr (applyLeftChanges χs ρ)
applyLeftChanges-⇑ʳᶜorr [] ρ = refl
applyLeftChanges-⇑ʳᶜorr (χ ∷ χs) ρ =
  trans
    (cong (applyLeftChanges χs) (applyLeftChange-⇑ʳᶜorr χ ρ))
    (applyLeftChanges-⇑ʳᶜorr χs (applyLeftChange χ ρ))

corr-⇑ʳᶜorr-inv :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL (suc ΔR) (⇑ʳᶜorr ρ) →
  StoreCorr ΔL ΔR ρ
corr-⇑ʳᶜorr-inv {ρ = ρ} corr =
  store-corr
    (subst (λ Σ → StoreDetWf _ Σ)
      (leftStore-⇑ʳᶜorr ρ)
      (leftStore-det corr))
    (StoreDetWf-⟰ᵗ-inv
      (subst (λ Σ → StoreDetWf _ Σ)
        (rightStore-⇑ʳᶜorr ρ)
        (rightStore-det corr)))
