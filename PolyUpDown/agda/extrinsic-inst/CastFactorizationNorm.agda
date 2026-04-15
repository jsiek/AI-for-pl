module CastFactorizationNorm where

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

postulate
  ⊑ᶜ⨾↑ˢ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ⊑ᶜ B
    → Σ ∣ Φ ⊢ B ↑ˢ C
    → Σ[ D ∈ Ty ] ((Σ ∣ Φ ⊢ B ↑ˢ D) × (Σ ∣ Φ ⊢ A ⊑ᶜ D))

  ↓ˢ⨾⊒ᶜ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ↓ˢ B
    → Σ ∣ Φ ⊢ B ⊒ᶜ C
    → Σ[ D ∈ Ty ] ((Σ ∣ Φ ⊢ D ⊒ᶜ C) × (Σ ∣ Φ ⊢ A ↓ˢ D))

postulate
  wt⊑-factor-norm-post :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Up}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ↑ˢ C) × (Σ ∣ Φ ⊢ C ⊑ᶜ B))

  wt⊒-factor-norm-post :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Down}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ⊒ᶜ C) × (Σ ∣ Φ ⊢ C ↓ˢ B))

mutual
  wt⊑-factor-norm :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Up}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊑ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ↑ˢ C) × (Σ ∣ Φ ⊢ C ⊑ᶜ B))
  wt⊑-factor-norm (wt-tag {G = G} g ok) =
    G , (↑ˢ-id (wfTySome G) , ⊑ᶜ-tag g ok)
  wt⊑-factor-norm (wt-unseal {A = A} hα α∈Φ) =
    A , (↑ˢ-unseal hα α∈Φ , ⊑ᶜ-id (wfTySome A))
  wt⊑-factor-norm (wt-unseal★ {α = α} hα α∈Φ) =
    ｀ α , (↑ˢ-id (wfTySome (｀ α)) , ⊑ᶜ-unseal★ {α = α} hα α∈Φ)
  wt⊑-factor-norm p = wt⊑-factor-norm-post p

  wt⊒-factor-norm :
    ∀ {Σ : Store}{Φ : List CastPerm}{p : Down}{A B : Ty}
    → Σ ∣ Φ ⊢ p ⦂ A ⊒ B
    → Σ[ C ∈ Ty ] ((Σ ∣ Φ ⊢ A ⊒ᶜ C) × (Σ ∣ Φ ⊢ C ↓ˢ B))
  wt⊒-factor-norm (wt-untag {G = G} g ok ℓ) =
    G , (⊒ᶜ-untag g ok ℓ , ↓ˢ-id (wfTySome G))
  wt⊒-factor-norm (wt-seal {A = A} hα α∈Φ) =
    A , (⊒ᶜ-id (wfTySome A) , ↓ˢ-seal hα α∈Φ)
  wt⊒-factor-norm (wt-seal★ {α = α} hα α∈Φ) =
    ｀ α , (⊒ᶜ-seal★ {α = α} hα α∈Φ , ↓ˢ-id (wfTySome (｀ α)))
  wt⊒-factor-norm p = wt⊒-factor-norm-post p
