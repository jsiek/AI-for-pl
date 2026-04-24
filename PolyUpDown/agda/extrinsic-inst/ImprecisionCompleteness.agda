module ImprecisionCompleteness where

-- File Charter:
--   * Completeness bridge from `Cast` back to unindexed `Imprecision`.
--   * Together with `ImprecisionBridge`, this gives soundness/completeness of
--   * imprecision with respect to `Cast`.

open import Types
open import Imprecision
open import Cast

mutual
  cast⊑⇒imprecision⊑ : ∀ {Σ Φ A B} → Σ ∣ Φ ⊢ A ⊑ᶜ B → A ⊑ B
  cast⊑⇒imprecision⊑ (⊑ᶜ-tag g ok) = ⊑-★ _ _ g ⊑-refl
  cast⊑⇒imprecision⊑ (⊑ᶜ-unseal★ {α} h α∈Φ) =
    ⊑-★ _ _ (｀ α) (⊑-｀ α)
  cast⊑⇒imprecision⊑ (⊑ᶜ-⇒ p q) =
    ⊑-⇒ _ _ _ _ (cast⊒⇒imprecision⊒ p) (cast⊑⇒imprecision⊑ q)
  cast⊑⇒imprecision⊑ (⊑ᶜ-∀ p) = ⊑-∀ _ _ (cast⊑⇒imprecision⊑ p)
  cast⊑⇒imprecision⊑ (⊑ᶜ-ν p) = ⊑-ν _ _ (cast⊑⇒imprecision⊑ p)
  cast⊑⇒imprecision⊑ (⊑ᶜ-id wfA) = ⊑-refl
  cast⊑⇒imprecision⊑ (p ；⊑ᶜ q) = ⊑-trans (cast⊑⇒imprecision⊑ p) (cast⊑⇒imprecision⊑ q)

  cast⊒⇒imprecision⊒ : ∀ {Σ Φ A B} → Σ ∣ Φ ⊢ A ⊒ᶜ B → A ⊒ B
  cast⊒⇒imprecision⊒ (⊒ᶜ-untag g ok ℓ) = ⊑-★ _ _ g ⊑-refl
  cast⊒⇒imprecision⊒ (⊒ᶜ-seal★ {α} h α∈Φ) =
    ⊑-★ _ _ (｀ α) (⊑-｀ α)
  cast⊒⇒imprecision⊒ (⊒ᶜ-⇒ p q) =
    ⊑-⇒ _ _ _ _ (cast⊑⇒imprecision⊑ p) (cast⊒⇒imprecision⊒ q)
  cast⊒⇒imprecision⊒ (⊒ᶜ-∀ p) = ⊑-∀ _ _ (cast⊒⇒imprecision⊒ p)
  cast⊒⇒imprecision⊒ (⊒ᶜ-ν p) = ⊑-ν _ _ (cast⊒⇒imprecision⊒ p)
  cast⊒⇒imprecision⊒ (⊒ᶜ-id wfA) = ⊑-refl
  cast⊒⇒imprecision⊒ (p ；⊒ᶜ q) = ⊒-trans (cast⊒⇒imprecision⊒ p) (cast⊒⇒imprecision⊒ q)
