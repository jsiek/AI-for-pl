module Conversion where

-- File Charter:
--   * Raw PolyConvert reveal/conceal conversion syntax and typing judgments.
--   * Conversion terms are store-independent syntax; their judgments check
--     store-indexed seal replacement structure.
--   * This file owns the conversion surface used by PolyConvert terms.

open import Data.Nat using (ℕ; suc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)

open import Types
open import Store

Label : Set
Label = ℕ

------------------------------------------------------------------------
-- Raw conversion evidence
------------------------------------------------------------------------

mutual
  data Conv↑ : Set where
    ↑-unseal : Seal → Conv↑
    ↑-⇒ : Conv↓ → Conv↑ → Conv↑
    ↑-∀ : Conv↑ → Conv↑
    ↑-id : Ty → Conv↑

  data Conv↓ : Set where
    ↓-seal : Seal → Conv↓
    ↓-⇒ : Conv↑ → Conv↓ → Conv↓
    ↓-∀ : Conv↓ → Conv↓
    ↓-id : Ty → Conv↓

mutual
  src↑ : Store → Conv↑ → Ty
  src↑ Σ (↑-unseal α) = ｀ α
  src↑ Σ (↑-⇒ p q) = tgt↓ Σ p ⇒ src↑ Σ q
  src↑ Σ (↑-∀ c) = `∀ (src↑ (⟰ᵗ Σ) c)
  src↑ Σ (↑-id A) = A

  tgt↑ : Store → Conv↑ → Ty
  tgt↑ Σ (↑-unseal α) = lookupTyˢ Σ α
  tgt↑ Σ (↑-⇒ p q) = src↓ Σ p ⇒ tgt↑ Σ q
  tgt↑ Σ (↑-∀ c) = `∀ (tgt↑ (⟰ᵗ Σ) c)
  tgt↑ Σ (↑-id A) = A

  src↓ : Store → Conv↓ → Ty
  src↓ Σ (↓-seal α) = lookupTyˢ Σ α
  src↓ Σ (↓-⇒ p q) = tgt↑ Σ p ⇒ src↓ Σ q
  src↓ Σ (↓-∀ c) = `∀ (src↓ (⟰ᵗ Σ) c)
  src↓ Σ (↓-id A) = A

  tgt↓ : Store → Conv↓ → Ty
  tgt↓ Σ (↓-seal α) = ｀ α
  tgt↓ Σ (↓-⇒ p q) = src↑ Σ p ⇒ tgt↓ Σ q
  tgt↓ Σ (↓-∀ c) = `∀ (tgt↓ (⟰ᵗ Σ) c)
  tgt↓ Σ (↓-id A) = A

mutual
  substConv↑ᵗ : Substᵗ → Conv↑ → Conv↑
  substConv↑ᵗ σ (↑-unseal α) = ↑-unseal α
  substConv↑ᵗ σ (↑-⇒ p q) =
    ↑-⇒ (substConv↓ᵗ σ p) (substConv↑ᵗ σ q)
  substConv↑ᵗ σ (↑-∀ c) = ↑-∀ (substConv↑ᵗ (extsᵗ σ) c)
  substConv↑ᵗ σ (↑-id A) = ↑-id (substᵗ σ A)

  substConv↓ᵗ : Substᵗ → Conv↓ → Conv↓
  substConv↓ᵗ σ (↓-seal α) = ↓-seal α
  substConv↓ᵗ σ (↓-⇒ p q) =
    ↓-⇒ (substConv↑ᵗ σ p) (substConv↓ᵗ σ q)
  substConv↓ᵗ σ (↓-∀ c) = ↓-∀ (substConv↓ᵗ (extsᵗ σ) c)
  substConv↓ᵗ σ (↓-id A) = ↓-id (substᵗ σ A)

mutual
  convert↑ : Ty → Seal → Conv↑
  convert↑ (＇ X) α = ↑-id (＇ X)
  convert↑ (｀ β) α with seal-≟ β α
  convert↑ (｀ β) α | yes _ = ↑-unseal α
  convert↑ (｀ β) α | no _ = ↑-id (｀ β)
  convert↑ (‵ ι) α = ↑-id (‵ ι)
  convert↑ ★ α = ↑-id ★
  convert↑ (A ⇒ B) α = ↑-⇒ (convert↓ A α) (convert↑ B α)
  convert↑ (`∀ A) α = ↑-∀ (convert↑ A α)

  convert↓ : Ty → Seal → Conv↓
  convert↓ (＇ X) α = ↓-id (＇ X)
  convert↓ (｀ β) α with seal-≟ β α
  convert↓ (｀ β) α | yes _ = ↓-seal α
  convert↓ (｀ β) α | no _ = ↓-id (｀ β)
  convert↓ (‵ ι) α = ↓-id (‵ ι)
  convert↓ ★ α = ↓-id ★
  convert↓ (A ⇒ B) α = ↓-⇒ (convert↑ A α) (convert↓ B α)
  convert↓ (`∀ A) α = ↓-∀ (convert↓ A α)

------------------------------------------------------------------------
-- Conversion typing: store-driven seal replacement structure
------------------------------------------------------------------------

infix 4 _∣_∣_⊢_⦂_↑ˢ_ _∣_∣_⊢_⦂_↓ˢ_

mutual
  data _∣_∣_⊢_⦂_↑ˢ_ (Δ : TyCtx) (Ψ : SealCtx)
      (Σ : Store) : Conv↑ → Ty → Ty → Set where
    ⊢↑-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → Δ ∣ Ψ ∣ Σ ⊢ ↑-unseal α ⦂ ｀ α ↑ˢ A

    ⊢↑-⇒ : ∀ {A A′ B B′ p q}
      → Δ ∣ Ψ ∣ Σ ⊢ p ⦂ A′ ↓ˢ A
      → Δ ∣ Ψ ∣ Σ ⊢ q ⦂ B ↑ˢ B′
      → Δ ∣ Ψ ∣ Σ ⊢ ↑-⇒ p q ⦂ (A ⇒ B) ↑ˢ (A′ ⇒ B′)

    ⊢↑-∀ : ∀ {A B c}
      → suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↑ˢ B
      → Δ ∣ Ψ ∣ Σ ⊢ ↑-∀ c ⦂ (`∀ A) ↑ˢ (`∀ B)

    ⊢↑-id : ∀ {A}
      → WfTy Δ Ψ A
      → Δ ∣ Ψ ∣ Σ ⊢ ↑-id A ⦂ A ↑ˢ A

  data _∣_∣_⊢_⦂_↓ˢ_ (Δ : TyCtx) (Ψ : SealCtx)
      (Σ : Store) : Conv↓ → Ty → Ty → Set where
    ⊢↓-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → Δ ∣ Ψ ∣ Σ ⊢ ↓-seal α ⦂ A ↓ˢ ｀ α

    ⊢↓-⇒ : ∀ {A A′ B B′ p q}
      → Δ ∣ Ψ ∣ Σ ⊢ p ⦂ A′ ↑ˢ A
      → Δ ∣ Ψ ∣ Σ ⊢ q ⦂ B ↓ˢ B′
      → Δ ∣ Ψ ∣ Σ ⊢ ↓-⇒ p q ⦂ (A ⇒ B) ↓ˢ (A′ ⇒ B′)

    ⊢↓-∀ : ∀ {A B c}
      → suc Δ ∣ Ψ ∣ ⟰ᵗ Σ ⊢ c ⦂ A ↓ˢ B
      → Δ ∣ Ψ ∣ Σ ⊢ ↓-∀ c ⦂ (`∀ A) ↓ˢ (`∀ B)

    ⊢↓-id : ∀ {A}
      → WfTy Δ Ψ A
      → Δ ∣ Ψ ∣ Σ ⊢ ↓-id A ⦂ A ↓ˢ A

------------------------------------------------------------------------
-- Endpoint correctness
------------------------------------------------------------------------

mutual
  src↑-correct :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    src↑ Σ c ≡ A
  src↑-correct wfΣ (⊢↑-unseal h) = refl
  src↑-correct wfΣ (⊢↑-⇒ p⊢ q⊢) =
    cong₂ _⇒_ (tgt↓-correct wfΣ p⊢) (src↑-correct wfΣ q⊢)
  src↑-correct wfΣ (⊢↑-∀ c⊢) =
    cong `∀ (src↑-correct (storeWf-⟰ᵗ wfΣ) c⊢)
  src↑-correct wfΣ (⊢↑-id wfA) = refl

  tgt↑-correct :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    tgt↑ Σ c ≡ B
  tgt↑-correct wfΣ (⊢↑-unseal h) =
    lookupTyˢ-lookup (storeWf-unique wfΣ) h
  tgt↑-correct wfΣ (⊢↑-⇒ p⊢ q⊢) =
    cong₂ _⇒_ (src↓-correct wfΣ p⊢) (tgt↑-correct wfΣ q⊢)
  tgt↑-correct wfΣ (⊢↑-∀ c⊢) =
    cong `∀ (tgt↑-correct (storeWf-⟰ᵗ wfΣ) c⊢)
  tgt↑-correct wfΣ (⊢↑-id wfA) = refl

  src↓-correct :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    src↓ Σ c ≡ A
  src↓-correct wfΣ (⊢↓-seal h) =
    lookupTyˢ-lookup (storeWf-unique wfΣ) h
  src↓-correct wfΣ (⊢↓-⇒ p⊢ q⊢) =
    cong₂ _⇒_ (tgt↑-correct wfΣ p⊢) (src↓-correct wfΣ q⊢)
  src↓-correct wfΣ (⊢↓-∀ c⊢) =
    cong `∀ (src↓-correct (storeWf-⟰ᵗ wfΣ) c⊢)
  src↓-correct wfΣ (⊢↓-id wfA) = refl

  tgt↓-correct :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    tgt↓ Σ c ≡ B
  tgt↓-correct wfΣ (⊢↓-seal h) = refl
  tgt↓-correct wfΣ (⊢↓-⇒ p⊢ q⊢) =
    cong₂ _⇒_ (src↑-correct wfΣ p⊢) (tgt↓-correct wfΣ q⊢)
  tgt↓-correct wfΣ (⊢↓-∀ c⊢) =
    cong `∀ (tgt↓-correct (storeWf-⟰ᵗ wfΣ) c⊢)
  tgt↓-correct wfΣ (⊢↓-id wfA) = refl

------------------------------------------------------------------------
-- Endpoint well-formedness
------------------------------------------------------------------------

mutual
  src↑-wf :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    WfTy Δ Ψ (src↑ Σ c)
  src↑-wf wfΣ (⊢↑-unseal h) = wfSeal (storeWf-dom< wfΣ h)
  src↑-wf wfΣ (⊢↑-⇒ p⊢ q⊢) =
    wf⇒ (tgt↓-wf wfΣ p⊢) (src↑-wf wfΣ q⊢)
  src↑-wf wfΣ (⊢↑-∀ c⊢) =
    wf∀ (src↑-wf (storeWf-⟰ᵗ wfΣ) c⊢)
  src↑-wf wfΣ (⊢↑-id wfA) = wfA

  tgt↑-wf :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B →
    WfTy Δ Ψ (tgt↑ Σ c)
  tgt↑-wf wfΣ (⊢↑-unseal h) =
    subst
      (WfTy _ _)
      (sym (lookupTyˢ-lookup (storeWf-unique wfΣ) h))
      (storeWf-wfTy wfΣ h)
  tgt↑-wf wfΣ (⊢↑-⇒ p⊢ q⊢) =
    wf⇒ (src↓-wf wfΣ p⊢) (tgt↑-wf wfΣ q⊢)
  tgt↑-wf wfΣ (⊢↑-∀ c⊢) =
    wf∀ (tgt↑-wf (storeWf-⟰ᵗ wfΣ) c⊢)
  tgt↑-wf wfΣ (⊢↑-id wfA) = wfA

  src↓-wf :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    WfTy Δ Ψ (src↓ Σ c)
  src↓-wf wfΣ (⊢↓-seal h) =
    subst
      (WfTy _ _)
      (sym (lookupTyˢ-lookup (storeWf-unique wfΣ) h))
      (storeWf-wfTy wfΣ h)
  src↓-wf wfΣ (⊢↓-⇒ p⊢ q⊢) =
    wf⇒ (tgt↑-wf wfΣ p⊢) (src↓-wf wfΣ q⊢)
  src↓-wf wfΣ (⊢↓-∀ c⊢) =
    wf∀ (src↓-wf (storeWf-⟰ᵗ wfΣ) c⊢)
  src↓-wf wfΣ (⊢↓-id wfA) = wfA

  tgt↓-wf :
    ∀ {Δ Ψ Σ c A B} →
    StoreWf Δ Ψ Σ →
    Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B →
    WfTy Δ Ψ (tgt↓ Σ c)
  tgt↓-wf wfΣ (⊢↓-seal h) = wfSeal (storeWf-dom< wfΣ h)
  tgt↓-wf wfΣ (⊢↓-⇒ p⊢ q⊢) =
    wf⇒ (src↑-wf wfΣ p⊢) (tgt↓-wf wfΣ q⊢)
  tgt↓-wf wfΣ (⊢↓-∀ c⊢) =
    wf∀ (tgt↓-wf (storeWf-⟰ᵗ wfΣ) c⊢)
  tgt↓-wf wfΣ (⊢↓-id wfA) = wfA
