module ImprecisionTheorems where

-- File Charter:
--   * Exposes public composition and dual operators for typed imprecision.
--   * Returns each produced coercion together with its imprecision derivation.
--   * Delegates implementations to the corresponding `proof` modules.

open import Data.Product using (Σ-syntax)

open import Coercions using (Coercion)
open import NarrowWiden
open import proof.ImprecisionComposition using
  ( narrowing-composition
  ; widening-composition
  )
open import proof.ImprecisionDual using
  ( narrowing-dual
  ; widening-dual
  )

------------------------------------------------------------------------
-- Narrowing and widening duality
------------------------------------------------------------------------

dualⁿ : ∀ {c : Coercion}{Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → Σ[ d ∈ Coercion ] Φ ∣ Δᴿ ⊢ d ⦂ B ⊑ A ⊣ Δᴸ
dualⁿ = narrowing-dual

dualʷ : ∀ {c : Coercion}{Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴿ
  → Σ[ d ∈ Coercion ] Φ ∣ Δᴿ ⊢ d ⦂ B ⊒ A ⊣ Δᴸ
dualʷ = widening-dual

------------------------------------------------------------------------
-- Narrowing and widening composition
------------------------------------------------------------------------

infixl 7 _⨟ⁿ_
infixl 7 _⨟ʷ_

_⨟ⁿ_ : ∀ {c d : Coercion}{Φ Δᴸ Δᴿ A B C}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ
_⨟ⁿ_ = narrowing-composition

_⨟ʷ_ : ∀ {c d : Coercion}{Φ Δᴸ Δᴿ A B C}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ d ⦂ B ⊑ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ
_⨟ʷ_ = widening-composition
