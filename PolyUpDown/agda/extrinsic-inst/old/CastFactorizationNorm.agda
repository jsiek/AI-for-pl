module CastFactorizationNorm where

-- UNDER CONSTRUCTION
-- TODO: Needs to be updated to reflect changes to UpDownNorm

-- File Charter:
--   * Initial factorization development for normalized Up/Down witnesses.
--   * Uses `ConversionNorm` and `CastNorm`, which remove generic composition
--   * constructors from derivation syntax.
--   * This file starts the theorem with base cases and leaves the hard cut-style
--   * composition interactions as explicit postulates for the next phase.

open import Data.List using (List)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

open import Types
open import Store
open import UpDown using (CastPerm; wfTySome)
open import UpDownNorm
open import ConversionNorm
open import CastNorm

mutual
  wt⊑-factor-norm :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Up}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ↑ˢ C) × (Σ ∣ Φ ⊢ C ⊑ᶜ B))
  wt⊑-factor-norm (wt-；tag p g ok) with wt⊑-factor-norm p
  wt⊑-factor-norm (wt-；tag p g ok) | C , (h↑ , h⊑) =
    C , (h↑ , ⊑ᶜ-；tag h⊑ g ok)
  wt⊑-factor-norm (wt-unseal； hα α∈Φ p) with wt⊑-factor-norm p
  wt⊑-factor-norm (wt-unseal； hα α∈Φ p) | C , (h↑ , h⊑) =
    C , (↑ˢ-unseal； hα α∈Φ h↑ , h⊑)
  wt⊑-factor-norm (wt-unseal★； hα α∈Φ q) with wt⊑-factor-norm q
  wt⊑-factor-norm (wt-unseal★； hα α∈Φ wt-q) | C , (h↑ , h⊑) =
  {-
      hα: Σ ∋ˢ α ⦂ ★
      α ∈cast Φ
      wt-q: Σ ∣ Φ ⊢ q ⦂ ★ ⊑ B

      h↑  : Σ₁ ∣ Φ ⊢ ★ ↑ˢ C     h⊑  : Σ₁ ∣ Φ ⊢ C ⊑ᶜ B

      nts
      Σ₁ ∣ Φ ⊢ ｀ α ↑ˢ ?0    Σ₁ ∣ Φ ⊢ ?0 ⊑ᶜ B
      
  -}
      {!!} , {!!} , {!!}
  wt⊑-factor-norm (wt-↦ p q) with wt⊒-factor-norm p | wt⊑-factor-norm q
  wt⊑-factor-norm (wt-↦ p q) | C₁ , (h⊒ , h↓) | C₂ , (h↑ , h⊑) =
    (C₁ ⇒ C₂) , (↑ˢ-⇒ h↓ h↑ , ⊑ᶜ-⇒ h⊒ h⊑)
  wt⊑-factor-norm (wt-∀ p) with wt⊑-factor-norm p
  wt⊑-factor-norm (wt-∀ p) | C , (h↑ , h⊑) =
    `∀ C , (↑ˢ-∀ h↑ , ⊑ᶜ-∀ h⊑)
  wt⊑-factor-norm (wt-ν q) = {!!}
  wt⊑-factor-norm {A = A} (wt-id wfA) =
    A , (↑ˢ-id wfA , ⊑ᶜ-id wfA)

  wt⊒-factor-norm :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Down}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ⊒ᶜ C) × (Σ ∣ Φ ⊢ C ↓ˢ B))
  wt⊒-factor-norm (wt-untag； g ok ℓ p) with wt⊒-factor-norm p
  wt⊒-factor-norm (wt-untag； g ok ℓ p) | C , (h⊒ , h↓) =
    C , (⊒ᶜ-untag； g ok ℓ h⊒ , h↓)
  wt⊒-factor-norm (wt-；seal p hα α∈Φ) with wt⊒-factor-norm p
  wt⊒-factor-norm (wt-；seal p hα α∈Φ) | C , (h⊒ , h↓) =
    C , (h⊒ , ↓ˢ-；seal h↓ hα α∈Φ)
  wt⊒-factor-norm (wt-；seal★ q hα α∈Φ) = {!!}
  wt⊒-factor-norm (wt-↦ p q) with wt⊑-factor-norm p | wt⊒-factor-norm q
  wt⊒-factor-norm (wt-↦ p q) | C₁ , (h↑ , h⊑) | C₂ , (h⊒ , h↓) =
    (C₁ ⇒ C₂) , (⊒ᶜ-⇒ h⊑ h⊒ , ↓ˢ-⇒ h↑ h↓)
  wt⊒-factor-norm (wt-∀ p) with wt⊒-factor-norm p
  wt⊒-factor-norm (wt-∀ p) | C , (h⊒ , h↓) =
    `∀ C , (⊒ᶜ-∀ h⊒ , ↓ˢ-∀ h↓)
  wt⊒-factor-norm (wt-ν q) = {!!}
  wt⊒-factor-norm {A = A} (wt-id wfA) =
    A , (⊒ᶜ-id wfA , ↓ˢ-id wfA)
