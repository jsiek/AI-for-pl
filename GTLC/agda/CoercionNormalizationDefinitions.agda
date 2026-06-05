module CoercionNormalizationDefinitions where

-- File Charter:
--   * Public coercion reduction vocabulary used to state coercion
--     normalization.
--   * Defines coercion one-step reduction, multi-step reduction, equivalence
--     up to administrative laws, and irreducibility.
--   * Quotiented coercion implementation details live under `proof/`.

open import Relation.Binary.PropositionalEquality using (_≢_)
open import Relation.Nullary using (¬_)

open import Types
open import Coercions

infix 4 _—→ᶜʳ_
infix 4 _—↠ᶜʳ_
infix 4 _≈ᶜʳ_
infix 4 _—↠≈ᶜʳ_
infix 4 _;ᶜʳ_—→_
infix 3 _∎ᶜʳ
infixr 2 _—→ᶜʳ⟨_⟩_

data _;ᶜʳ_—→_ : Coercion → Coercion → Coercion → Set where
  β-idLᶜʳ : ∀ {A c}
    → idᶜ A ;ᶜʳ c —→ c

  β-idRᶜʳ : ∀ {B c}
    → c ;ᶜʳ idᶜ B —→ c

  β-proj-inj-okᶜʳ : ∀ {G ℓ}
    → G ! ;ᶜʳ ((_`? {ℓ = ℓ}) G) —→ idᶜ G

  β-proj-inj-badᶜʳ : ∀ {G H ℓ}
    → G ≢ H
    → G ! ;ᶜʳ ((_`? {ℓ = ℓ}) H) —→ (⊥ᶜ G ⇨ H at ℓ)

  β-↦ᶜʳ : ∀ {c d c′ d′}
    → (c ↦ d) ;ᶜʳ (c′ ↦ d′) —→ ((c′ ⨟ c) ↦ (d ⨟ d′))

  β-⊥Lᶜʳ : ∀ {A B C d ℓ}
    → ⊢ d ⦂ B ⇨ C
    → (⊥ᶜ A ⇨ B at ℓ) ;ᶜʳ d —→ (⊥ᶜ A ⇨ C at ℓ)

  β-!⊥ᶜʳ : ∀ {G B ℓ}
    → G ! ;ᶜʳ (⊥ᶜ ★ ⇨ B at ℓ) —→ (⊥ᶜ G ⇨ B at ℓ)

  β-↦⊥ᶜʳ : ∀ {c d A B C D E ℓ}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → (c ↦ d) ;ᶜʳ (⊥ᶜ (C ⇒ D) ⇨ E at ℓ)
      —→ (⊥ᶜ (A ⇒ B) ⇨ E at ℓ)

data _—→ᶜʳ_ : Coercion → Coercion → Set where
  ξ-pairᶜʳ : ∀ {c d e}
    → c ;ᶜʳ d —→ e
    → (c ⨟ d) —→ᶜʳ e

  ξ-⨟₁ᶜʳ : ∀ {c c′ d}
    → c —→ᶜʳ c′
    → (c ⨟ d) —→ᶜʳ (c′ ⨟ d)

  ξ-⨟₂ᶜʳ : ∀ {c d d′}
    → d —→ᶜʳ d′
    → (c ⨟ d) —→ᶜʳ (c ⨟ d′)

  ξ-↦₁ᶜʳ : ∀ {c c′ d}
    → c —→ᶜʳ c′
    → (c ↦ d) —→ᶜʳ (c′ ↦ d)

  ξ-↦₂ᶜʳ : ∀ {c d d′}
    → d —→ᶜʳ d′
    → (c ↦ d) —→ᶜʳ (c ↦ d′)

data _—↠ᶜʳ_ : Coercion → Coercion → Set where
  _∎ᶜʳ : (c : Coercion) → c —↠ᶜʳ c

  _—→ᶜʳ⟨_⟩_ : (c : Coercion) {d e : Coercion}
    → c —→ᶜʳ d
    → d —↠ᶜʳ e
    → c —↠ᶜʳ e

data _≈ᶜʳ_ : Coercion → Coercion → Set where
  ≈ᶜʳ-refl : ∀ {c}
    → c ≈ᶜʳ c

  ≈ᶜʳ-sym : ∀ {c d}
    → c ≈ᶜʳ d
    → d ≈ᶜʳ c

  ≈ᶜʳ-trans : ∀ {c d e}
    → c ≈ᶜʳ d
    → d ≈ᶜʳ e
    → c ≈ᶜʳ e

  ≈ᶜʳ-⨟ : ∀ {c c′ d d′}
    → c ≈ᶜʳ c′
    → d ≈ᶜʳ d′
    → (c ⨟ d) ≈ᶜʳ (c′ ⨟ d′)

  ≈ᶜʳ-↦ : ∀ {c c′ d d′}
    → c ≈ᶜʳ c′
    → d ≈ᶜʳ d′
    → (c ↦ d) ≈ᶜʳ (c′ ↦ d′)

  ≈ᶜʳ-idL : ∀ {A c}
    → (idᶜ A ⨟ c) ≈ᶜʳ c

  ≈ᶜʳ-idR : ∀ {B c}
    → (c ⨟ idᶜ B) ≈ᶜʳ c

  ≈ᶜʳ-assoc : ∀ {c d e}
    → ((c ⨟ d) ⨟ e) ≈ᶜʳ (c ⨟ (d ⨟ e))

data _—↠≈ᶜʳ_ : Coercion → Coercion → Set where
  ≈ᶜʳ-done : ∀ {c d}
    → c ≈ᶜʳ d
    → c —↠≈ᶜʳ d

  step≈ᶜʳ : ∀ {c d e}
    → c —→ᶜʳ d
    → d —↠≈ᶜʳ e
    → c —↠≈ᶜʳ e

  eq≈ᶜʳ : ∀ {c d e}
    → c ≈ᶜʳ d
    → d —↠≈ᶜʳ e
    → c —↠≈ᶜʳ e

record Irreducible (c : Coercion) : Set where
  constructor irred
  field
    no-step : ∀ {d} → ¬ (c —→ᶜʳ d)
