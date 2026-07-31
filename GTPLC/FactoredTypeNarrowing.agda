module FactoredTypeNarrowing where

-- File Charter:
--   * Defines factored type narrowing for two related type contexts.
--   * Factors each derivation into type relocation followed by one-context
--     coercion narrowing on the right.
--   * Provides the structural operators used by term and environment
--     narrowing.
--   * Depends on TypeRelocate for all relocation-only operations.

open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import Coercions
open import TypeRelocate
open import NarrowWiden using
  ( _∣_∣_⊢_⊒_
  )
open import ImprecisionTheorems using (dualⁿ)
open import proof.ImprecisionRenaming using (⇑ⁿ-ext; ⇑ⁿ-gen)

------------------------------------------------------------------------
-- Factored type narrowing
------------------------------------------------------------------------

infix 4 _⊢_⊒ᶠ_
infixr 5 _⨟ᶠ_

record _⊢_⊒ᶠ_ {Δᴸ Δᴿ}
    (Φ : ImpCtx Δᴸ Δᴿ) (A B : Ty) : Set where
  constructor _⨟ᶠ_
  field
    {middle} : Ty
    relocation : Φ ⊢ A ≈ middle
    narrowing : precisionMode Φ ∣ Δᴿ ∣ [] ⊢ middle ⊒ B

open _⊢_⊒ᶠ_ public

factor-src-wf : ∀ {Δᴸ Δᴿ Φ A B}
  → (p : _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A B)
  → WfTy Δᴸ A
factor-src-wf (r ⨟ᶠ p) = ≈-src-wf r

factor-tgt-wf : ∀ {Δᴸ Δᴿ Φ A B}
  → (p : _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A B)
  → WfTy Δᴿ B
factor-tgt-wf (r ⨟ᶠ (_ , p)) = NarrowWiden.⊒-tgt-wf p

------------------------------------------------------------------------
-- Structural operators
------------------------------------------------------------------------

infixr 6 _↦ᶠ_

_↦ᶠ_ : ∀ {Δᴸ Δᴿ Φ A A′ B B′}
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A A′
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ B B′
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ (A ⇒ B) (A′ ⇒ B′)
(rA ⨟ᶠ p) ↦ᶠ (rB ⨟ᶠ q) with dualⁿ p
... | c , c⊑ with q
...   | d , d⊒ =
  (rA ⇒ʳ rB) ⨟ᶠ ((c Coercions.↦ d) , (c⊑ NarrowWiden.↦ d⊒))

∀ᶠ_ : ∀ {Δᴸ Δᴿ Φ A B}
  → _⊢_⊒ᶠ_ {suc Δᴸ} {suc Δᴿ} (bothᵢ Φ) A B
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ (`∀ A) (`∀ B)
∀ᶠ (r ⨟ᶠ (c , c⊒)) =
  ∀ʳ r ⨟ᶠ (Coercions.`∀ c , NarrowWiden.∀ⁿ c⊒)

genᶠ : ∀ {Δᴸ Δᴿ Φ Ψ A B}
  → (extension : SmartExtensionᵢ Φ Ψ)
  → NonVar A
  → zero ∈ᵗ A
  → _⊢_⊒ᶠ_ {Δᴸ} {suc Δᴿ} Ψ B A
  → B ≢ ★
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ B (`∀ A)
genᶠ extension nonvarA zero∈A p B≢★ = {!!}

⇑ᶠ : ∀ {Δᴸ Δᴿ Φ A B}
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A B
  → _⊢_⊒ᶠ_ {suc Δᴸ} {suc Δᴿ}
      (bothᵢ Φ) (⇑ᵗ A) (⇑ᵗ B)
⇑ᶠ (r ⨟ᶠ p) = ⇑ʳ r ⨟ᶠ ⇑ⁿ-ext p

⇑ᴿᶠ : ∀ {Δᴸ Δᴿ Φ A B}
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A B
  → _⊢_⊒ᶠ_ {Δᴸ} {suc Δᴿ} (freshᴿ Φ) A (⇑ᵗ B)
⇑ᴿᶠ (r ⨟ᶠ p) = ⇑ᴿʳ r ⨟ᶠ ⇑ⁿ-gen p

smart-⇑ᴿᶠ : ∀ {Δᴸ Δᴿ Φ Ψ A B}
  → (extension : SmartExtensionᵢ Φ Ψ)
  → _⊢_⊒ᶠ_ {Δᴸ} {Δᴿ} Φ A B
  → _⊢_⊒ᶠ_ {Δᴸ} {suc Δᴿ} Ψ A (⇑ᵗ B)
smart-⇑ᴿᶠ freshᵢ p = ⇑ᴿᶠ p
smart-⇑ᴿᶠ reuseᵢ p = {!!}
