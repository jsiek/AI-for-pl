module ImprecisionTheorems where

-- File Charter:
--   * Exposes public composition and dual operators for typed imprecision.
--   * Takes and returns coercions bundled with their typing derivations.
--   * Builds universal narrowings from bundled body evidence.
--   * Builds function narrowings from bundled domain and codomain evidence.
--   * Compares bundled narrowings by propositional coercion equality.
--   * Delegates implementations to the corresponding `proof` modules.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (_∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Coercions using (renameᶜ)
  renaming (_↦_ to _↦ᶜ_; `∀ to ∀ᶜ; gen to genᶜ)
open import NarrowWiden hiding (_↦_; ∀ⁿ_; gen)
open import NarrowWiden using ()
  renaming (_↦_ to _↦ⁱ_; ∀ⁿ_ to ∀ⁿⁱ_; gen to genⁱ)
open import Types using (_⇒_; NonVar; _∈ᵗ_; ★; `∀; ⇑ᵗ)
open import proof.ImprecisionComposition using
  ( narrowing-composition
  ; narrowing-composition-left
  ; narrowing-lift
  ; target-liftⁿ
  ; widening-composition
  )
open import proof.ImprecisionDual using
  ( narrowing-dual
  ; widening-dual
  )

------------------------------------------------------------------------
-- Narrowing and widening duality
------------------------------------------------------------------------

dualⁿ : ∀ {Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → Φ ∣ Δᴿ ⊢ B ⊑ A ⊣ Δᴸ
dualⁿ (c , cⁿ) = narrowing-dual cⁿ

dualʷ : ∀ {Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  → Φ ∣ Δᴿ ⊢ B ⊒ A ⊣ Δᴸ
dualʷ (c , cʷ) = widening-dual cʷ

------------------------------------------------------------------------
-- Narrowing under type-context extension
------------------------------------------------------------------------

⇑ⁿ : ∀ {Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ⇑ᵗ A ⊒ ⇑ᵗ B ⊣ suc Δᴿ
⇑ⁿ (c , cⁿ) = renameᶜ suc c , narrowing-lift cⁿ

⇑ᴿⁿ : ∀ {Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ Δᴸ ⊢ A ⊒ ⇑ᵗ B ⊣ suc Δᴿ
⇑ᴿⁿ (c , cⁿ) = renameᶜ suc c , target-liftⁿ cⁿ

------------------------------------------------------------------------
-- Bundled polymorphic narrowing
------------------------------------------------------------------------

∀ⁿ_ : ∀ {Φ Δᴸ Δᴿ A B}
  → ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊒ B ⊣ suc Δᴿ
  → Φ ∣ Δᴸ ⊢ `∀ A ⊒ `∀ B ⊣ Δᴿ
∀ⁿ (c , c⊒) = ∀ᶜ c , ∀ⁿⁱ c⊒

gen : ∀ {Φ Δᴸ Δᴿ A B}
  → NonVar A
  → zero ∈ᵗ A
  → ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ∣ Δᴸ ⊢ B ⊒ A ⊣ suc Δᴿ
  → B ≢ ★
  → Φ ∣ Δᴸ ⊢ B ⊒ `∀ A ⊣ Δᴿ
gen nonvarA zero∈A (c , c⊒) B≢★ =
  genᶜ c , genⁱ nonvarA zero∈A c⊒ B≢★

------------------------------------------------------------------------
-- Narrowing and widening composition
------------------------------------------------------------------------

infixr 6 _↦_
infixl 7 _⨟ⁿ_
infixl 7 _⨟ˡⁿ_
infixl 7 _⨟ʷ_
infix 4 _≐ⁿ_

_↦_ : ∀ {Φ Δᴸ Δᴿ A A′ B B′}
  → Φ ∣ Δᴿ ⊢ A′ ⊑ A ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ B ⊒ B′ ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ A ⇒ B ⊒ A′ ⇒ B′ ⊣ Δᴿ
(c , cʷ) ↦ (d , dⁿ) = (c ↦ᶜ d , cʷ ↦ⁱ dⁿ)

_⨟ⁿ_ : ∀ {Φ Δᴸ Δᴿ A B C}
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → idᵢ Δᴿ ∣ Δᴿ ⊢ B ⊒ C ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ A ⊒ C ⊣ Δᴿ
(c , cⁿ) ⨟ⁿ (d , dⁿ) = narrowing-composition cⁿ dⁿ

_⨟ˡⁿ_ : ∀ {Φ Δᴸ Δᴿ A B C}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ B ⊒ C ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ A ⊒ C ⊣ Δᴿ
(c , cⁿ) ⨟ˡⁿ (d , dⁿ) =
  narrowing-composition-left cⁿ dⁿ

_⨟ʷ_ : ∀ {Φ Δᴸ Δᴿ A B C}
  → idᵢ Δᴸ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴸ
  → Φ ∣ Δᴸ ⊢ B ⊑ C ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ
(c , cʷ) ⨟ʷ (d , dʷ) = widening-composition cʷ dʷ

_≐ⁿ_ : ∀ {Φ Δᴸ Δᴿ A B}
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → Φ ∣ Δᴸ ⊢ A ⊒ B ⊣ Δᴿ
  → Set
p ≐ⁿ q = proj₁ p ≡ proj₁ q
