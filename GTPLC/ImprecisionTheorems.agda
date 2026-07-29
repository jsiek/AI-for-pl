module ImprecisionTheorems where

-- File Charter:
--   * Exposes public composition operators for typed narrowings and widenings.
--   * Returns the composed coercion together with its imprecision derivation.
--   * Delegates the implementation to `proof.ImprecisionComposition`.

open import Data.Product using (Σ-syntax)

open import Coercions using (Coercion)
open import NarrowWiden
open import proof.ImprecisionComposition using
  ( narrowing-composition-total
  ; widening-composition-total
  )

------------------------------------------------------------------------
-- Narrowing and widening composition
------------------------------------------------------------------------

infixl 7 _⨟ⁿ_
infixl 7 _⨟ʷ_

_⨟ⁿ_ : ∀ {c d Φ Δᴸ Δᴿ A B C}
  → Φ ∣ Δᴸ ⊢ c ⦂ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ d ⦂ B ⊒ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊒ C ⊣ Δᴿ
_⨟ⁿ_ = narrowing-composition-total

_⨟ʷ_ : ∀ {c d Φ Δᴸ Δᴿ A B C}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ c ⦂ A ⊑ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ d ⦂ B ⊑ C ⊣ Δᴿ
  → Σ[ r ∈ Coercion ] Φ ∣ Δᴸ ⊢ r ⦂ A ⊑ C ⊣ Δᴿ
_⨟ʷ_ = widening-composition-total
