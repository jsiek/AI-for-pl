module alt.Store where

-- File Charter:
--   * Defines the append-only store of runtime type names.
--   * Store entries are scoped only by names allocated earlier in the store.
--   * Lookup exposes entries weakened to the current store length; appending
--     weakens existing lookups without traversing any term.

open import Data.Fin using (Fin; fromℕ; inject₁)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types

Name : Set
Name = ℕ

data Store : ℕ → Set where
  empty : Store 0
  bind : ∀ {n} → Store n → Ty n → Store (suc n)

infix 4 _⦂_∈_

data _⦂_∈_ : ∀ {n} → Name → Ty n → Store n → Set where
  here : ∀ {n} {Σ : Store n} {R : Ty n} {S : Ty (suc n)}
    → S ≡ ⇑ᵗ R
      -------------------
    → n ⦂ S ∈ bind Σ R

  there : ∀ {n α} {Σ : Store n} {R A : Ty n} {B : Ty (suc n)}
    → α ⦂ A ∈ Σ
    → B ≡ ⇑ᵗ A
      -------------------
    → α ⦂ B ∈ bind Σ R

lookup-name : ∀ {n α} {Σ : Store n} {R : Ty n}
  → α ⦂ R ∈ Σ
  → Fin n
lookup-name (here refl) = fromℕ _
lookup-name (there p refl) = inject₁ (lookup-name p)

weaken-lookup : ∀ {n α} {Σ : Store n} {R A : Ty n}
  → α ⦂ A ∈ Σ
  → α ⦂ ⇑ᵗ A ∈ bind Σ R
weaken-lookup p = there p refl

fresh-lookup : ∀ {n} {Σ : Store n} {R : Ty n}
  → n ⦂ ⇑ᵗ R ∈ bind Σ R
fresh-lookup = here refl
