module ConversionNorm where

-- File Charter:
--   * Normalized Conversion judgments without a generic composition constructor.
--   * Rule shapes are a subset of `UpDownNorm` Up/Down typing rules:
--   * include `seal`/`unseal` boundaries, but exclude `tag`/`untag` and `ν`.
--   * Composition at conversion boundaries is represented by dedicated
--   * `unseal`/`seal`-flavored constructors.
--   * Exposes explicit composition lemmas (`compose↑ˢ`, `compose↓ˢ`) instead of
--   * a transitivity constructor in the syntax of derivations.

open import Data.List using (List; _∷_)

open import Types
open import TypeProperties
open import Store
open import UpDown using (CastPerm; _∈conv_; WfTySome)

infix 4 _∣_⊢_↑ˢ_ _∣_⊢_↓ˢ_

mutual
  data _∣_⊢_↑ˢ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where

    ↑ˢ-unseal； : ∀ {α A B}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↑ˢ B
      → Σ ∣ Φ ⊢ ｀ α ↑ˢ B

    ↑ˢ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ↓ˢ A
      → Σ ∣ Φ ⊢ B ↑ˢ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ↑ˢ (A′ ⇒ B′)

    ↑ˢ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ↑ˢ B
      → Σ ∣ Φ ⊢ (`∀ A) ↑ˢ (`∀ B)

    ↑ˢ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ↑ˢ A

  data _∣_⊢_↓ˢ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where

    ↓ˢ-；seal : ∀ {A α B}
      → Σ ∣ Φ ⊢ A ↓ˢ B
      → Σ ∋ˢ α ⦂ B
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↓ˢ ｀ α

    ↓ˢ-⇒ : ∀ {A A′ B B′}
      → Σ ∣ Φ ⊢ A′ ↑ˢ A
      → Σ ∣ Φ ⊢ B ↓ˢ B′
      → Σ ∣ Φ ⊢ (A ⇒ B) ↓ˢ (A′ ⇒ B′)

    ↓ˢ-∀ : ∀ {A B}
      → ⟰ᵗ Σ ∣ Φ ⊢ A ↓ˢ B
      → Σ ∣ Φ ⊢ (`∀ A) ↓ˢ (`∀ B)

    ↓ˢ-id : ∀ {A}
      → WfTySome A
      → Σ ∣ Φ ⊢ A ↓ˢ A

postulate
  compose↑ˢ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ↑ˢ B
    → Σ ∣ Φ ⊢ B ↑ˢ C
    → Σ ∣ Φ ⊢ A ↑ˢ C

  compose↓ˢ :
    ∀ {Σ : Store}{Φ : List CastPerm}{A B C : Ty}
    → Σ ∣ Φ ⊢ A ↓ˢ B
    → Σ ∣ Φ ⊢ B ↓ˢ C
    → Σ ∣ Φ ⊢ A ↓ˢ C
