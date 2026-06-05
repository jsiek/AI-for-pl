module proof.CoercionEquality where

open import Agda.Builtin.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
open import proof.CoercionReduction

infix 4 _≈_

data _≈_ : Coercion → Coercion → Set where
  ≈-refl : ∀ {c}
    → c ≈ c

  ≈-sym : ∀ {c d}
    → c ≈ d
    → d ≈ c

  ≈-trans : ∀ {c d e}
    → c ≈ d
    → d ≈ e
    → c ≈ e

  ≈-↦ : ∀ {c₁ c₂ d₁ d₂}
    → c₁ ≈ c₂
    → d₁ ≈ d₂
    → singleᶜ (c₁ ↦ d₁) ≈ singleᶜ (c₂ ↦ d₂)

  ≈-⨟ : ∀ {c₁ c₂ d₁ d₂}
    → c₁ ≈ c₂
    → d₁ ≈ d₂
    → (c₁ ⨟ d₁) ≈ (c₂ ⨟ d₂)

  -- Rules mirroring one-step reduction rules.
  ≈-β-proj-inj-ok : ∀ {G ℓ}
    → singleᶜ (G !) ⨟ singleᶜ (G ？ ℓ) ≈ []

  ≈-β-proj-inj-bad : ∀ {G H ℓ}
    → G ≢ H
    → singleᶜ (G !) ⨟ singleᶜ (H ？ ℓ)
      ≈ singleᶜ (⊥ᶜ G ⇨ H at ℓ)

  ≈-β-idL : ∀ {d}
    → [] ⨟ d ≈ d

  ≈-β-idR : ∀ {c}
    → c ⨟ [] ≈ c

  ≈-β-assocL : ∀ {c₁ c₂ c₃}
    → (c₁ ⨟ (c₂ ⨟ c₃)) ≈ ((c₁ ⨟ c₂) ⨟ c₃)

  ≈-β-assocR : ∀ {c₁ c₂ c₃}
    → ((c₁ ⨟ c₂) ⨟ c₃) ≈ (c₁ ⨟ (c₂ ⨟ c₃))

  ≈-β-↦ : ∀ {c d c′ d′}
    → singleᶜ (c ↦ d) ⨟ singleᶜ (c′ ↦ d′)
      ≈ singleᶜ ((c′ ⨟ c) ↦ (d ⨟ d′))

  ≈-β-⊥L : ∀ {A B C d ℓ}
    → ⊢ d ⦂ B ⇨ᶜ C
    → singleᶜ (⊥ᶜ A ⇨ B at ℓ) ⨟ singleᶜ d
      ≈ singleᶜ (⊥ᶜ A ⇨ C at ℓ)

  ≈-β-!⊥ : ∀ {G B ℓ}
    → singleᶜ (G !) ⨟ singleᶜ (⊥ᶜ ★ ⇨ B at ℓ)
      ≈ singleᶜ (⊥ᶜ G ⇨ B at ℓ)

  ≈-β-↦⊥ : ∀ {c d A B C D E ℓ}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → singleᶜ (c ↦ d) ⨟ singleᶜ (⊥ᶜ (C ⇒ D) ⇨ E at ℓ)
      ≈ singleᶜ (⊥ᶜ (A ⇒ B) ⇨ E at ℓ)

—→⇒≈ : ∀ {c d}
  → c —→ d
  → c ≈ d
—→⇒≈ (ξ-pair β-proj-inj-okᶜ refl) =
  ≈-⨟ ≈-β-proj-inj-ok ≈-refl
—→⇒≈ (ξ-pair (β-proj-inj-badᶜ G≢H) refl) =
  ≈-⨟ (≈-β-proj-inj-bad G≢H) ≈-refl
—→⇒≈ (ξ-pair β-↦ᶜ refl) =
  ≈-⨟ ≈-β-↦ ≈-refl
—→⇒≈ (ξ-pair (β-⊥Lᶜ dwt) refl) =
  ≈-⨟ (≈-β-⊥L dwt) ≈-refl
—→⇒≈ (ξ-pair β-!⊥ᶜ refl) =
  ≈-⨟ ≈-β-!⊥ ≈-refl
—→⇒≈ (ξ-pair (β-↦⊥ᶜ cwt dwt) refl) =
  ≈-⨟ (≈-β-↦⊥ cwt dwt) ≈-refl
—→⇒≈ (ξ-∷ᶜ {c = c} c→c′) =
  ≈-⨟ {c₁ = singleᶜ c} ≈-refl (—→⇒≈ c→c′)
—→⇒≈ (ξ-↦₁ᶜ {d = d} {cs = cs} c→c′) =
  ≈-⨟ {d₁ = cs} (≈-↦ (—→⇒≈ c→c′) ≈-refl) ≈-refl
—→⇒≈ (ξ-↦₂ᶜ {c = c} {cs = cs} d→d′) =
  ≈-⨟ {d₁ = cs} (≈-↦ ≈-refl (—→⇒≈ d→d′)) ≈-refl

—↠⇒≈ : ∀ {c d}
  → c —↠ d
  → c ≈ d
—↠⇒≈ (_ ∎) = ≈-refl
—↠⇒≈ (_ —→⟨ c→c₁ ⟩ c₁↠d) =
  ≈-trans (—→⇒≈ c→c₁) (—↠⇒≈ c₁↠d)

≈-complete : ∀ {c d c′}
  → c —↠ c′
  → d —↠ c′
  → c ≈ d
≈-complete c↠c′ d↠c′ =
  ≈-trans (—↠⇒≈ c↠c′) (≈-sym (—↠⇒≈ d↠c′))
