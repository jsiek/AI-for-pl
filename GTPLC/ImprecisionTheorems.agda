module ImprecisionTheorems where

-- File Charter:
--   * Public API for GTPLC narrowing and widening duality/composition.
--   * States the public operations explicitly over bundled derivations.
--   * Delegates proof implementations to `proof.ImprecisionDual` and
--     `proof.ImprecisionComposition`.

open import Data.Product using (proj₂)

open import Types
open import TyStore
open import Coercions
open import NarrowWiden
import proof.ImprecisionDual as Dual
import proof.ImprecisionComposition as Composition

------------------------------------------------------------------------
-- Duality
------------------------------------------------------------------------

dualⁿ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊑ A
dualⁿ p = Dual.narrowing-dual (proj₂ p)

dualʷ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊒ A
dualʷ p = Dual.widening-dual (proj₂ p)

------------------------------------------------------------------------
-- Composition
------------------------------------------------------------------------

infixl 6 _⨟ⁿ_
infixl 6 _⨟ʷ_

_⨟ⁿ_ : ∀ {μ Δ Σ A B C}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊒ C
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ C
_⨟ⁿ_ = Composition._⨟ⁿ_

_⨟ʷ_ : ∀ {μ Δ Σ A B C}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ B ⊑ C
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ C
_⨟ʷ_ = Composition._⨟ʷ_

------------------------------------------------------------------------
-- Equality of the bundled coercions
------------------------------------------------------------------------

infix 4 _≐ⁿ_
infix 4 _≐ʷ_

_≐ⁿ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊒ B
  → Set
_≐ⁿ_ = Composition._≐ⁿ_

_≐ʷ_ : ∀ {μ Δ Σ A B}
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → μ ∣ Δ ∣ Σ ⊢ A ⊑ B
  → Set
_≐ʷ_ = Composition._≐ʷ_
