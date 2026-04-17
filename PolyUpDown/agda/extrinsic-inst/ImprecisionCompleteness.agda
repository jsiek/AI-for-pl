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
  cast⊑⇒imprecision⊑ (⊑ᶜ-tag g ok) = ⊑-★ g ⊑-refl
  cast⊑⇒imprecision⊑ (⊑ᶜ-unseal★ {α} h α∈Φ) = ⊑-★ (｀ α) ⊑-｀
  cast⊑⇒imprecision⊑ (⊑ᶜ-⇒ p q) = ⊑-⇒ (cast⊒⇒imprecision⊒ p) (cast⊑⇒imprecision⊑ q)
  cast⊑⇒imprecision⊑ (⊑ᶜ-∀ p) = ⊑-∀ (cast⊑⇒imprecision⊑ p)
  cast⊑⇒imprecision⊑ (⊑ᶜ-ν p) = ⊑-ν (cast⊑⇒imprecision⊑ p)
  cast⊑⇒imprecision⊑ (⊑ᶜ-id wfA) = ⊑-refl
  cast⊑⇒imprecision⊑ (p ；⊑ᶜ q) = ⊑-trans (cast⊑⇒imprecision⊑ p) (cast⊑⇒imprecision⊑ q)

  cast⊒⇒imprecision⊒ : ∀ {Σ Φ A B} → Σ ∣ Φ ⊢ A ⊒ᶜ B → A ⊒ B
  cast⊒⇒imprecision⊒ (⊒ᶜ-untag g ok ℓ) = ⊑-★ g ⊑-refl
  cast⊒⇒imprecision⊒ (⊒ᶜ-seal★ {α} h α∈Φ) = ⊑-★ (｀ α) ⊑-｀
  cast⊒⇒imprecision⊒ (⊒ᶜ-⇒ p q) = ⊑-⇒ (cast⊑⇒imprecision⊑ p) (cast⊒⇒imprecision⊒ q)
  cast⊒⇒imprecision⊒ (⊒ᶜ-∀ p) = ⊑-∀ (cast⊒⇒imprecision⊒ p)
  cast⊒⇒imprecision⊒ (⊒ᶜ-ν p) = ⊑-ν (cast⊒⇒imprecision⊒ p)
  cast⊒⇒imprecision⊒ (⊒ᶜ-id wfA) = ⊑-refl
  cast⊒⇒imprecision⊒ (p ；⊒ᶜ q) = ⊒-trans (cast⊒⇒imprecision⊒ p) (cast⊒⇒imprecision⊒ q)
