module CastNorm where

-- File Charter:
--   * Normalized Cast judgments without a generic composition constructor.
--   * Rule shapes are a subset of `UpDownNorm` Up/Down typing rules:
--   * include `tag`/`untag`, `ν`, and cast-seal-based `seal★`/`unseal★`.
--   * Boundary-aware forms absorb local composition at primitive boundaries.
--   * Exposes explicit composition lemmas (`compose⊑ᶜ`, `compose⊒ᶜ`) for use in
--   * factorization proofs.

open import Data.List using (List; _∷_)
open import Data.Nat using (zero)
open import Data.Product using (_,_)

open import Types
open import TypeProperties
open import Store
open import UpDown
  using
    ( CastPerm
    ; Label
    ; cast-seal
    ; cast-tag
    ; _∈cast_
    ; ⊢_ok_
    ; WfTySome
    )

infix 4 _∣_⊢_⊑ᶜ_ _∣_⊢_⊒ᶜ_

mutual
  data _∣_⊢_⊑ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ⊑ᶜ-；tag : ∀ {A G}
      → Σ ∣ Φ ⊢ A ⊑ᶜ G
      → (g : Ground G)
      → ⊢ g ok Φ
      → Σ ∣ Φ ⊢ A ⊑ᶜ ★

    ⊑ᶜ-unseal★； : ∀ {α B}
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ ★ ⊑ᶜ B
      → Σ ∣ Φ ⊢ ｀ α ⊑ᶜ B

    ⊑ᶜ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ⊒ᶜ A
      → Σ ∣ Φ ⊢ B ⊑ᶜ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ⊑ᶜ (A′ ⇒ B′)

    ⊑ᶜ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ⊑ᶜ B
      → Σ ∣ Φ ⊢ (`∀ A) ⊑ᶜ (`∀ B)

    ⊑ᶜ-ν : ∀ {A B}
      → ((zero , ★) ∷ ⟰ˢ Σ) ∣ (cast-seal ∷ Φ) ⊢ (⇑ˢ A) [ α₀ ]ᵗ ⊑ᶜ ⇑ˢ B
      → Σ ∣ Φ ⊢ `∀ A ⊑ᶜ B

    ⊑ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊑ᶜ A

  data _∣_⊢_⊒ᶜ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where

    ⊒ᶜ-untag； : ∀ {G B}
      → (g : Ground G)
      → ⊢ g ok Φ
      → (ℓ : Label)
      → Σ ∣ Φ ⊢ G ⊒ᶜ B
      → Σ ∣ Φ ⊢ ★ ⊒ᶜ B

    ⊒ᶜ-；seal★ : ∀ {A α}
      → Σ ∣ Φ ⊢ A ⊒ᶜ ★
      → Σ ∋ˢ α ⦂ ★
      → α ∈cast Φ
      → Σ ∣ Φ ⊢ A ⊒ᶜ ｀ α

    ⊒ᶜ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ⊑ᶜ A
      → Σ ∣ Φ ⊢ B ⊒ᶜ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ⊒ᶜ (A′ ⇒ B′)

    ⊒ᶜ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ⊒ᶜ B
      → Σ ∣ Φ ⊢ `∀ A ⊒ᶜ `∀ B

    ⊒ᶜ-ν : ∀ {A B}
      → ((zero , ⇑ˢ ★) ∷ ⟰ˢ Σ) ∣ (cast-tag ∷ Φ) ⊢ ⇑ˢ B ⊒ᶜ ((⇑ˢ A) [ α₀ ]ᵗ)
      → Σ ∣ Φ ⊢ B ⊒ᶜ `∀ A

    ⊒ᶜ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ⊒ᶜ A

postulate
  compose⊑ᶜ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ⊑ᶜ B
    → Σ ∣ Φ ⊢ B ⊑ᶜ C
    → Σ ∣ Φ ⊢ A ⊑ᶜ C

  compose⊒ᶜ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ⊒ᶜ B
    → Σ ∣ Φ ⊢ B ⊒ᶜ C
    → Σ ∣ Φ ⊢ A ⊒ᶜ C
