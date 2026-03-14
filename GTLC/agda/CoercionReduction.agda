module CoercionReduction where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Contexts
open import GTLC 

infixr 7 _⨟_
infixr 6 _↦_

-- This adds ⊥ compared to Coercion in Coercions.agda
data Coercion : Set where
  idᶜ  : Ty → Coercion
  _!   : Ty → Coercion -- injection (tagging)
  _`?  : Ty → Coercion -- projection (tag checking)
  _↦_  : Coercion → Coercion → Coercion
  _⨟_  : Coercion → Coercion → Coercion
  ⊥ᶜ_⇨_ : Ty → Ty → Coercion

data Atomic : Coercion → Set where
  atom-idᶜ : ∀ {A} → Atomic (idᶜ A)
  atom-! : ∀ {G} → Atomic (G !)
  atom-? : ∀ {G} → Atomic (G `?)

infix 4 ⊢_⦂_⇨_

data ⊢_⦂_⇨_ : Coercion → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → Ground G
    → ⊢ G ! ⦂ G ⇨ ★

  ⊢? : ∀ {G}
    → Ground G
    → ⊢ G `? ⦂ ★ ⇨ G

  ⊢↦ : ∀ {A B C D c d}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (C ⇒ D)

  ⊢⨟ : ∀ {A B C c d}
    → ⊢ c ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → ⊢ c ⨟ d ⦂ A ⇨ C

  ⊢⊥ : ∀ {A B}
    → ⊢ (⊥ᶜ A ⇨ B) ⦂ A ⇨ B

coerce : ∀ {A B} → A ~ B → Coercion
coerce ~-ℕ = idᶜ ℕ
coerce ~-★ = idᶜ ★
coerce ★~ℕ = ℕ `?
coerce ℕ~★ = ℕ !
coerce (★~⇒ c d) = (★ ⇒ ★) `? ⨟ (coerce c ↦ coerce d)
coerce (⇒~★ c d) = (coerce c ↦ coerce d) ⨟ ((★ ⇒ ★) !)
  --              A ⇒ B               ★ ⇒ ★            ★
coerce (~-⇒ c d) = coerce c ↦ coerce d

coerce-wt : ∀ {A B} (p : A ~ B) → ⊢ coerce p ⦂ A ⇨ B
coerce-wt ~-ℕ = ⊢idᶜ
coerce-wt ~-★ = ⊢idᶜ
coerce-wt ★~ℕ = ⊢? G-ℕ
coerce-wt ℕ~★ = ⊢! G-ℕ
coerce-wt (★~⇒ c d) =
  ⊢⨟ (⊢? G-⇒) (⊢↦ (coerce-wt c) (coerce-wt d))
coerce-wt (⇒~★ c d) =
  ⊢⨟ (⊢↦ (coerce-wt c) (coerce-wt d)) (⊢! G-⇒)
coerce-wt (~-⇒ c d) = ⊢↦ (coerce-wt c) (coerce-wt d)


coercion-type-unique : ∀ {c A B C D}
  → ⊢ c ⦂ A ⇨ B
  → ⊢ c ⦂ C ⇨ D
    -------------
  → A ≡ C × B ≡ D
coercion-type-unique ⊢idᶜ ⊢idᶜ = refl , refl
coercion-type-unique (⊢! g₁) (⊢! g₂) = refl , refl
coercion-type-unique (⊢? g₁) (⊢? g₂) = refl , refl
coercion-type-unique (⊢↦ c₁ d₁) (⊢↦ c₂ d₂)
  with coercion-type-unique c₁ c₂ | coercion-type-unique d₁ d₂
... | refl , refl | refl , refl = refl , refl
coercion-type-unique (⊢⨟ c₁ d₁) (⊢⨟ c₂ d₂)
  with coercion-type-unique c₁ c₂ | coercion-type-unique d₁ d₂
... | refl , refl | refl , refl = refl , refl
coercion-type-unique ⊢⊥ ⊢⊥ = refl , refl

----------------------------------------------------------------
-- Coercion Reduction
----------------------------------------------------------------

infix 4 _—→ᶜᶜ_
infix 3 _∎ᶜᶜ
infixr 2 _—→ᶜᶜ⟨_⟩_
infix 2 _—↠ᶜᶜ_

data _—→ᶜᶜ_ : Coercion → Coercion → Set where
  β-proj-inj-okᶜ : ∀ {G}
    → (G ! ⨟ G `?) —→ᶜᶜ idᶜ G

  β-proj-inj-badᶜ : ∀ {G H}
    → G ≢ H
    → (G ! ⨟ H `?) —→ᶜᶜ (⊥ᶜ G ⇨ H)

  β-idLᶜ : ∀ {A d}
    → (idᶜ A ⨟ d) —→ᶜᶜ d

  β-idRᶜ : ∀ {B c}
    → (c ⨟ idᶜ B) —→ᶜᶜ c

  β-assocLᶜ : ∀ {c₁ c₂ c₃}
    → (c₁ ⨟ (c₂ ⨟ c₃)) —→ᶜᶜ ((c₁ ⨟ c₂) ⨟ c₃)

  β-assocRᶜ : ∀ {c₁ c₂ c₃}
    → ((c₁ ⨟ c₂) ⨟ c₃) —→ᶜᶜ (c₁ ⨟ (c₂ ⨟ c₃))

  β-↦ᶜ : ∀ {c d c′ d′}
    → ((c ↦ d) ⨟ (c′ ↦ d′)) —→ᶜᶜ ((c′ ⨟ c) ↦ (d ⨟ d′))

  β-⊥Lᶜ : ∀ {A B C d}
    → ⊢ d ⦂ B ⇨ C
    → ((⊥ᶜ A ⇨ B) ⨟ d) —→ᶜᶜ (⊥ᶜ A ⇨ C)

  β-!⊥ᶜ : ∀ {G B}
    → (G ! ⨟ (⊥ᶜ ★ ⇨ B)) —→ᶜᶜ (⊥ᶜ G ⇨ B)

  β-↦⊥ᶜ : ∀ {c d A B C D E}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ((c ↦ d) ⨟ (⊥ᶜ (C ⇒ D) ⇨ E)) —→ᶜᶜ (⊥ᶜ (A ⇒ B) ⇨ E)

  ξ-⨟₁ᶜ : ∀ {c c′ d}
    → c —→ᶜᶜ c′
    → (c ⨟ d) —→ᶜᶜ (c′ ⨟ d)

  ξ-⨟₂ᶜ : ∀ {c d d′}
    → d —→ᶜᶜ d′
    → (c ⨟ d) —→ᶜᶜ (c ⨟ d′)

  ξ-↦₁ᶜ : ∀ {c c′ d}
    → c —→ᶜᶜ c′
    → (c ↦ d) —→ᶜᶜ (c′ ↦ d)

  ξ-↦₂ᶜ : ∀ {c d d′}
    → d —→ᶜᶜ d′
    → (c ↦ d) —→ᶜᶜ (c ↦ d′)

  -- consider adding:
  --  idᶜ A ↦ idᶜ B —→ᶜᶜ idᶜ (A ⇒ B)

data _—↠ᶜᶜ_ : Coercion → Coercion → Set where
  _∎ᶜᶜ : (c : Coercion) → c —↠ᶜᶜ c
  _—→ᶜᶜ⟨_⟩_ : (l : Coercion) {m n : Coercion}
    → l —→ᶜᶜ m
    → m —↠ᶜᶜ n
    → l —↠ᶜᶜ n

multi-transᶜᶜ : {c d e : Coercion}
  → c —↠ᶜᶜ d
  → d —↠ᶜᶜ e
  → c —↠ᶜᶜ e
multi-transᶜᶜ (_ ∎ᶜᶜ) ms2 = ms2
multi-transᶜᶜ (_ —→ᶜᶜ⟨ s ⟩ ms1′) ms2 =
  _ —→ᶜᶜ⟨ s ⟩ (multi-transᶜᶜ ms1′ ms2)

infixr 2 _—↠ᶜᶜ⟨_⟩_
_—↠ᶜᶜ⟨_⟩_ : ∀ (l : Coercion) {m n : Coercion}
  → l —↠ᶜᶜ m
  → m —↠ᶜᶜ n
  → l —↠ᶜᶜ n
l —↠ᶜᶜ⟨ l—↠m ⟩ m—↠n = multi-transᶜᶜ l—↠m m—↠n

preserve-—→ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —→ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—→ᶜᶜ (⊢⨟ (⊢! g) (⊢? g′)) β-proj-inj-okᶜ = ⊢idᶜ
preserve-—→ᶜᶜ (⊢⨟ (⊢! g) (⊢? g′)) (β-proj-inj-badᶜ G≢H) = ⊢⊥
preserve-—→ᶜᶜ (⊢⨟ ⊢idᶜ dwt) β-idLᶜ = dwt
preserve-—→ᶜᶜ (⊢⨟ cwt ⊢idᶜ) β-idRᶜ = cwt
preserve-—→ᶜᶜ (⊢⨟ cwt (⊢⨟ dwt ewt)) β-assocLᶜ = ⊢⨟ (⊢⨟ cwt dwt) ewt
preserve-—→ᶜᶜ (⊢⨟ (⊢⨟ cwt dwt) ewt) β-assocRᶜ = ⊢⨟ cwt (⊢⨟ dwt ewt)
preserve-—→ᶜᶜ (⊢⨟ (⊢↦ cwt dwt) (⊢↦ c′wt d′wt)) β-↦ᶜ =
  ⊢↦ (⊢⨟ c′wt cwt) (⊢⨟ dwt d′wt)
preserve-—→ᶜᶜ (⊢⨟ ⊢⊥ dwt) (β-⊥Lᶜ dwt′)
  with coercion-type-unique dwt dwt′
... | refl , refl = ⊢⊥
preserve-—→ᶜᶜ (⊢⨟ (⊢! g) ⊢⊥) β-!⊥ᶜ = ⊢⊥
preserve-—→ᶜᶜ (⊢⨟ (⊢↦ cwt dwt) ⊢⊥) (β-↦⊥ᶜ cwt′ dwt′)
  with coercion-type-unique cwt cwt′ | coercion-type-unique dwt dwt′
... | refl , refl | refl , refl = ⊢⊥
preserve-—→ᶜᶜ (⊢⨟ cwt dwt) (ξ-⨟₁ᶜ c→c′) =
  ⊢⨟ (preserve-—→ᶜᶜ cwt c→c′) dwt
preserve-—→ᶜᶜ (⊢⨟ cwt dwt) (ξ-⨟₂ᶜ d→d′) =
  ⊢⨟ cwt (preserve-—→ᶜᶜ dwt d→d′)
preserve-—→ᶜᶜ (⊢↦ cwt dwt) (ξ-↦₁ᶜ c→c′) =
  ⊢↦ (preserve-—→ᶜᶜ cwt c→c′) dwt
preserve-—→ᶜᶜ (⊢↦ cwt dwt) (ξ-↦₂ᶜ d→d′) =
  ⊢↦ cwt (preserve-—→ᶜᶜ dwt d→d′)

----------------------------------------------------------------
-- Coercion Normal Forms (up to associativity)
----------------------------------------------------------------

data Normalᶜ : Coercion → Set where
  nf-id : ∀ {A}
    → Normalᶜ (idᶜ A)

  nf-? : ∀ {G}
    → Ground G
    → Normalᶜ (G `?)

  nf-! : ∀ {G}
    → Ground G
    → Normalᶜ (G !)

  nf-?! : ∀ {G}
    → Ground G
    → Normalᶜ ((G `?) ⨟ (G !))

  nf-↦ : ∀ {c d}
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (c ↦ d)

  nf-?↦ : ∀ {G c d}
    → Ground G
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (G `? ⨟ (c ↦ d))

  nf-↦! : ∀ {c d G}
    → Normalᶜ c
    → Normalᶜ d
    → Ground G
    → Normalᶜ ((c ↦ d) ⨟ (G !))

  nf-?↦! : ∀ {G c d}
    → Ground G
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ (G `? ⨟ ((c ↦ d) ⨟ (G !)))

  nf-?↦!ˡ : ∀ {G c d}
    → Ground G
    → Normalᶜ c
    → Normalᶜ d
    → Normalᶜ ((G `? ⨟ (c ↦ d)) ⨟ (G !))

  nf-?⊥ : ∀ {G A B}
    → Ground G
    → Normalᶜ (G `? ⨟ (⊥ᶜ A ⇨ B))

  nf-⊥ : ∀ {A B}
    → Normalᶜ (⊥ᶜ A ⇨ B)

preserve-—↠ᶜᶜ : ∀ {c c′ A B}
  → ⊢ c ⦂ A ⇨ B
  → c —↠ᶜᶜ c′
  → ⊢ c′ ⦂ A ⇨ B
preserve-—↠ᶜᶜ cwt (_ ∎ᶜᶜ) = cwt
preserve-—↠ᶜᶜ cwt (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  preserve-—↠ᶜᶜ (preserve-—→ᶜᶜ cwt c→c₁) c₁↠c′

multi-ξ-⨟₁ᶜᶜ : ∀ {c c′ d}
  → c —↠ᶜᶜ c′
  → (c ⨟ d) —↠ᶜᶜ (c′ ⨟ d)
multi-ξ-⨟₁ᶜᶜ (_ ∎ᶜᶜ) = (_ ⨟ _) ∎ᶜᶜ
multi-ξ-⨟₁ᶜᶜ (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  (_ ⨟ _) —→ᶜᶜ⟨ ξ-⨟₁ᶜ c→c₁ ⟩ multi-ξ-⨟₁ᶜᶜ c₁↠c′

multi-ξ-⨟₂ᶜᶜ : ∀ {c d d′}
  → d —↠ᶜᶜ d′
  → (c ⨟ d) —↠ᶜᶜ (c ⨟ d′)
multi-ξ-⨟₂ᶜᶜ (_ ∎ᶜᶜ) = (_ ⨟ _) ∎ᶜᶜ
multi-ξ-⨟₂ᶜᶜ (_ —→ᶜᶜ⟨ d→d₁ ⟩ d₁↠d′) =
  (_ ⨟ _) —→ᶜᶜ⟨ ξ-⨟₂ᶜ d→d₁ ⟩ multi-ξ-⨟₂ᶜᶜ d₁↠d′

multi-ξ-↦₁ᶜᶜ : ∀ {c c′ d}
  → c —↠ᶜᶜ c′
  → (c ↦ d) —↠ᶜᶜ (c′ ↦ d)
multi-ξ-↦₁ᶜᶜ (_ ∎ᶜᶜ) = (_ ↦ _) ∎ᶜᶜ
multi-ξ-↦₁ᶜᶜ (_ —→ᶜᶜ⟨ c→c₁ ⟩ c₁↠c′) =
  (_ ↦ _) —→ᶜᶜ⟨ ξ-↦₁ᶜ c→c₁ ⟩ multi-ξ-↦₁ᶜᶜ c₁↠c′

multi-ξ-↦₂ᶜᶜ : ∀ {c d d′}
  → d —↠ᶜᶜ d′
  → (c ↦ d) —↠ᶜᶜ (c ↦ d′)
multi-ξ-↦₂ᶜᶜ (_ ∎ᶜᶜ) = (_ ↦ _) ∎ᶜᶜ
multi-ξ-↦₂ᶜᶜ (_ —→ᶜᶜ⟨ d→d₁ ⟩ d₁↠d′) =
  (_ ↦ _) —→ᶜᶜ⟨ ξ-↦₂ᶜ d→d₁ ⟩ multi-ξ-↦₂ᶜᶜ d₁↠d′
