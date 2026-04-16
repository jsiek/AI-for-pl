module ConversionNorm where

-- UNDER CONSTRUCTION
-- TODO: Needs to be updated to reflect changes to UpDownNorm

-- File Charter:
--   * Normalized Conversion judgments without a generic composition constructor.
--   * Composition at conversion boundaries is represented by dedicated
--   * unseal/seal-flavored constructors.
--   * Exposes explicit composition lemmas (`compose↑ˢ`, `compose↓ˢ`) instead of
--   * a transitivity constructor in the syntax of derivations.

open import Data.List using (List; _∷_)
open import Agda.Builtin.Equality using (_≡_)

open import Types
open import TypeProperties
open import Store
open import UpDown using (CastPerm; _∈conv_; WfTySome; lookupTyˢ)

infix 4 _∣_⊢_↑ˢ_ _∣_⊢_↓ˢ_

mutual
  data _∣_⊢_↑ˢ_ (Σ : Store) (Φ : List CastPerm) : Ty → Ty → Set where
    ↑ˢ-unseal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ ｀ α ↑ˢ A

    ↑ˢ-；unseal : ∀ {A α B}
      → Σ ∣ Φ ⊢ A ↑ˢ ｀ α
      → Σ ∋ˢ α ⦂ B
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↑ˢ B

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
    ↓ˢ-seal : ∀ {α A}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↓ˢ ｀ α

    ↓ˢ-；seal : ∀ {A α B}
      → Σ ∣ Φ ⊢ A ↓ˢ B
      → B ≡ lookupTyˢ Σ α
      → Σ ∋ˢ α ⦂ lookupTyˢ Σ α
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ A ↓ˢ ｀ α

    ↓ˢ-seal； : ∀ {α A B}
      → Σ ∋ˢ α ⦂ A
      → α ∈conv Φ
      → Σ ∣ Φ ⊢ ｀ α ↓ˢ B
      → Σ ∣ Φ ⊢ A ↓ˢ B

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
