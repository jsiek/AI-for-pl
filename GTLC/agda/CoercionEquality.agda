module CoercionEquality where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import CoercionReduction

infix 4 _≈ᶜ_

data _≈ᶜ_ : Coercion → Coercion → Set where
  ≈-refl : ∀ {c}
    → c ≈ᶜ c

  ≈-sym : ∀ {c d}
    → c ≈ᶜ d
    → d ≈ᶜ c

  ≈-trans : ∀ {c d e}
    → c ≈ᶜ d
    → d ≈ᶜ e
    → c ≈ᶜ e

  ≈-↦ : ∀ {c₁ c₂ d₁ d₂}
    → c₁ ≈ᶜ c₂
    → d₁ ≈ᶜ d₂
    → (c₁ ↦ d₁) ≈ᶜ (c₂ ↦ d₂)

  ≈-⨟ : ∀ {c₁ c₂ d₁ d₂}
    → c₁ ≈ᶜ c₂
    → d₁ ≈ᶜ d₂
    → (c₁ ⨟ d₁) ≈ᶜ (c₂ ⨟ d₂)

  -- Rules mirroring one-step reduction rules.
  ≈-β-proj-inj-ok : ∀ {G ℓ}
    → (G ! ⨟ ((_`? {ℓ = ℓ}) G)) ≈ᶜ idᶜ G

  ≈-β-proj-inj-bad : ∀ {G H ℓ}
    → G ≢ H
    → (G ! ⨟ ((_`? {ℓ = ℓ}) H)) ≈ᶜ (⊥ᶜ G ⇨ H)

  ≈-β-idL : ∀ {A d}
    → (idᶜ A ⨟ d) ≈ᶜ d

  ≈-β-idR : ∀ {B c}
    → (c ⨟ idᶜ B) ≈ᶜ c

  ≈-β-assocL : ∀ {c₁ c₂ c₃}
    → (c₁ ⨟ (c₂ ⨟ c₃)) ≈ᶜ ((c₁ ⨟ c₂) ⨟ c₃)

  ≈-β-assocR : ∀ {c₁ c₂ c₃}
    → ((c₁ ⨟ c₂) ⨟ c₃) ≈ᶜ (c₁ ⨟ (c₂ ⨟ c₃))

  ≈-β-↦ : ∀ {c d c′ d′}
    → ((c ↦ d) ⨟ (c′ ↦ d′)) ≈ᶜ ((c′ ⨟ c) ↦ (d ⨟ d′))

  ≈-β-⊥L : ∀ {A B C d}
    → ⊢ d ⦂ B ⇨ C
    → ((⊥ᶜ A ⇨ B) ⨟ d) ≈ᶜ (⊥ᶜ A ⇨ C)

  ≈-β-!⊥ : ∀ {G B}
    → (G ! ⨟ (⊥ᶜ ★ ⇨ B)) ≈ᶜ (⊥ᶜ G ⇨ B)

  ≈-β-↦⊥ : ∀ {c d A B C D E}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ((c ↦ d) ⨟ (⊥ᶜ (C ⇒ D) ⇨ E)) ≈ᶜ (⊥ᶜ (A ⇒ B) ⇨ E)

—→ᶜᶜ⇒≈ᶜ : ∀ {c d}
  → c —→ᶜᶜ d
  → c ≈ᶜ d
—→ᶜᶜ⇒≈ᶜ β-proj-inj-okᶜ = ≈-β-proj-inj-ok
—→ᶜᶜ⇒≈ᶜ (β-proj-inj-badᶜ G≢H) = ≈-β-proj-inj-bad G≢H
—→ᶜᶜ⇒≈ᶜ β-idLᶜ = ≈-β-idL
—→ᶜᶜ⇒≈ᶜ β-idRᶜ = ≈-β-idR
—→ᶜᶜ⇒≈ᶜ β-assocLᶜ = ≈-β-assocL
—→ᶜᶜ⇒≈ᶜ β-assocRᶜ = ≈-β-assocR
—→ᶜᶜ⇒≈ᶜ β-↦ᶜ = ≈-β-↦
—→ᶜᶜ⇒≈ᶜ (β-⊥Lᶜ dwt) = ≈-β-⊥L dwt
—→ᶜᶜ⇒≈ᶜ β-!⊥ᶜ = ≈-β-!⊥
—→ᶜᶜ⇒≈ᶜ (β-↦⊥ᶜ cwt dwt) = ≈-β-↦⊥ cwt dwt
—→ᶜᶜ⇒≈ᶜ (ξ-⨟₁ᶜ c→c′) = ≈-⨟ (—→ᶜᶜ⇒≈ᶜ c→c′) ≈-refl
—→ᶜᶜ⇒≈ᶜ (ξ-⨟₂ᶜ d→d′) = ≈-⨟ ≈-refl (—→ᶜᶜ⇒≈ᶜ d→d′)
—→ᶜᶜ⇒≈ᶜ (ξ-↦₁ᶜ c→c′) = ≈-↦ (—→ᶜᶜ⇒≈ᶜ c→c′) ≈-refl
—→ᶜᶜ⇒≈ᶜ (ξ-↦₂ᶜ d→d′) = ≈-↦ ≈-refl (—→ᶜᶜ⇒≈ᶜ d→d′)

—↠ᶜᶜ⇒≈ᶜ : ∀ {c d}
  → c —↠ᶜᶜ d
  → c ≈ᶜ d
—↠ᶜᶜ⇒≈ᶜ (_ ∎ᶜᶜ) = ≈-refl
—↠ᶜᶜ⇒≈ᶜ (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠d) =
  ≈-trans (—→ᶜᶜ⇒≈ᶜ c→c₁) (—↠ᶜᶜ⇒≈ᶜ c₁↠d)

≈ᶜ-complete : ∀ {c d c′}
  → c —↠ᶜᶜ c′
  → d —↠ᶜᶜ c′
  → c ≈ᶜ d
≈ᶜ-complete c↠c′ d↠c′ =
  ≈-trans (—↠ᶜᶜ⇒≈ᶜ c↠c′) (≈-sym (—↠ᶜᶜ⇒≈ᶜ d↠c′))
