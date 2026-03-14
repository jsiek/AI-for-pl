module Coercions where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Contexts
open import GTLC 

infixr 7 _⨟_
infixr 6 _↦_

data Coercion : Set where
  idᶜ  : Ty → Coercion
  _!   : Ty → Coercion -- injection (tagging)
  _`?  : Ty → Coercion -- projection (tag checking)
  _↦_  : Coercion → Coercion → Coercion
  _⨟_  : Coercion → Coercion → Coercion

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

----------------------------------------------------------------
-- Coercion Precision
----------------------------------------------------------------

infix 4 _⊑ᶜ_

data _⊑ᶜ_ : Coercion → Coercion → Set where
  -- congruence rules
  ⊑idᶜ : ∀ {A A′} → A′ ⊑ A
     → idᶜ A′ ⊑ᶜ idᶜ A
  ⊑!   : ∀ {A A′} → A′ ⊑ A
     → A′ ! ⊑ᶜ A !
  ⊑?   : ∀ {A A′} → A′ ⊑ A
     → A′ `? ⊑ᶜ A `?
  ⊑↦   : ∀ {c c′ d d′} → c′ ⊑ᶜ c → d′ ⊑ᶜ d
     → (c′ ↦ d′) ⊑ᶜ (c ↦ d)
  ⊑⨟   : ∀ {c c′ d d′} → c′ ⊑ᶜ c → d′ ⊑ᶜ d
     → (c′ ⨟ d′) ⊑ᶜ (c ⨟ d)

  -- rules relating identity to other coercions
  ⊑idL  : ∀ {A B C c} → Atomic c → ⊢ c ⦂ B ⇨ C → A ⊑ B → A ⊑ C
     → idᶜ A ⊑ᶜ c
  ⊑idL↦★ : ∀ {c d} → idᶜ ★ ⊑ᶜ c → idᶜ ★ ⊑ᶜ d
    → idᶜ ★ ⊑ᶜ (c ↦ d)
  ⊑idL↦ : ∀ {A B c d} → idᶜ A ⊑ᶜ c → idᶜ B ⊑ᶜ d → idᶜ (A ⇒ B) ⊑ᶜ (c ↦ d)
  ⊑idL⨟ : ∀ {A c d} → idᶜ A ⊑ᶜ c → idᶜ A ⊑ᶜ d → idᶜ A ⊑ᶜ (c ⨟ d)
  ⊑idR  : ∀ {A B C c} → Atomic c → ⊢ c ⦂ B ⇨ C → B ⊑ A → C ⊑ A → c ⊑ᶜ idᶜ A
  ⊑idR↦ : ∀ {A B c d} → c ⊑ᶜ idᶜ A → d ⊑ᶜ idᶜ B
    → (c ↦ d) ⊑ᶜ idᶜ (A ⇒ B)
  ⊑idR⨟ : ∀ {A c d} → c ⊑ᶜ idᶜ A → d ⊑ᶜ idᶜ A → (c ⨟ d) ⊑ᶜ idᶜ A
  
  ⊑drop? : ∀ {c c′}
    → c′ ⊑ᶜ c
    → ((★ ⇒ ★) `? ⨟ c′) ⊑ᶜ c
  ⊑drop! : ∀ {c c′}
    → c′ ⊑ᶜ c
    → (c′ ⨟ ((★ ⇒ ★) !)) ⊑ᶜ c

⊑ᶜ-reflexive : ∀ {c} → c ⊑ᶜ c
⊑ᶜ-reflexive {c = idᶜ A} = ⊑idᶜ ⊑-refl
⊑ᶜ-reflexive {c = A !} = ⊑! ⊑-refl
⊑ᶜ-reflexive {c = A `?} = ⊑? ⊑-refl
⊑ᶜ-reflexive {c = c ↦ d} = ⊑↦ ⊑ᶜ-reflexive ⊑ᶜ-reflexive
⊑ᶜ-reflexive {c = c ⨟ d} = ⊑⨟ ⊑ᶜ-reflexive ⊑ᶜ-reflexive

⊑id★ : ∀ {c A B} → ⊢ c ⦂ A ⇨ B → idᶜ ★ ⊑ᶜ c
⊑id★ ⊢idᶜ = ⊑idᶜ ⊑-★
⊑id★ (⊢! g) = ⊑idL atom-! (⊢! g) ⊑-★ ⊑-★
⊑id★ (⊢? g) = ⊑idL atom-? (⊢? g) ⊑-★ ⊑-★
⊑id★ (⊢↦ cwt dwt) = ⊑idL↦★ (⊑id★ cwt) (⊑id★ dwt)
⊑id★ (⊢⨟ cwt dwt) = ⊑idL⨟ (⊑id★ cwt) (⊑id★ dwt)

coerce-monotonic
  : ∀ {A A′ B B′}
  → A′ ⊑ A
  → (c : A ~ B)
  → B′ ⊑ B
  → (d : A′ ~ B′)
  → coerce d ⊑ᶜ coerce c
coerce-monotonic A′⊑A ~-ℕ B′⊑B ~-ℕ = ⊑idᶜ ⊑-ℕ
coerce-monotonic A′⊑A ~-ℕ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-monotonic A′⊑A ~-ℕ B′⊑B ★~ℕ = ⊑idR atom-? (⊢? G-ℕ) A′⊑A ⊑-refl
coerce-monotonic A′⊑A ~-ℕ B′⊑B ℕ~★ = ⊑idR atom-! (⊢! G-ℕ) A′⊑A ⊑-★
coerce-monotonic A′⊑A ~-★ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-monotonic A′⊑A ★~ℕ B′⊑B ~-★ = ⊑idL atom-? (⊢? G-ℕ) A′⊑A ⊑-★
coerce-monotonic A′⊑A ★~ℕ B′⊑B ★~ℕ = ⊑? ⊑-refl
coerce-monotonic A′⊑A ℕ~★ B′⊑B ~-★ = ⊑idL atom-! (⊢! G-ℕ) A′⊑A ⊑-★
coerce-monotonic A′⊑A ℕ~★ B′⊑B ℕ~★ = ⊑! ⊑-refl
coerce-monotonic A′⊑A (★~⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟ (⊑idL atom-? (⊢? G-⇒) A′⊑A ⊑-★)
        (⊑idL↦★
          (⊑id★ (coerce-wt c₁))
          (⊑id★ (coerce-wt c₂)))
coerce-monotonic A′⊑A (★~⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑⨟
    (⊑? ⊑-refl)
    (⊑↦
      (coerce-monotonic B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-monotonic ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-monotonic A′⊑A (⇒~★ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟
        (⊑idL↦★
          (⊑id★ (coerce-wt c₁))
          (⊑id★ (coerce-wt c₂)))
        (⊑idL atom-! (⊢! G-⇒) ⊑-★ ⊑-★)
coerce-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (⇒~★ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑⨟
    (⊑↦
      (coerce-monotonic ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-monotonic A′₂⊑A₂ c₂ ⊑-★ d₂))
    (⊑! ⊑-refl)
coerce-monotonic A′⊑A (~-⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL↦★
    (⊑id★ (coerce-wt c₁))
    (⊑id★ (coerce-wt c₂))
coerce-monotonic A′⊑A (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑drop?
    (⊑↦
      (coerce-monotonic B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-monotonic ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑drop!
    (⊑↦
      (coerce-monotonic ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-monotonic A′₂⊑A₂ c₂ ⊑-★ d₂))
coerce-monotonic (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (~-⇒ d₁ d₂) =
  ⊑↦
    (coerce-monotonic B′₁⊑B₁ c₁ A′₁⊑A₁ d₁)
    (coerce-monotonic A′₂⊑A₂ c₂ B′₂⊑B₂ d₂)

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

⊑ᶜ→⊑ : ∀ {c c′ A B A′ B′ }
    → ⊢ c ⦂ A ⇨ B → ⊢ c′ ⦂ A′ ⇨ B′
    → c′ ⊑ᶜ c
      ----------------
    → A′ ⊑ A × B′ ⊑ B
⊑ᶜ→⊑ ⊢idᶜ ⊢idᶜ (⊑idᶜ A′⊑A) = A′⊑A , A′⊑A
⊑ᶜ→⊑ ⊢c ⊢c′ (⊑idL {A = A₀} atomic c p q)
  with coercion-type-unique ⊢c c | coercion-type-unique ⊢c′ (⊢idᶜ {A = A₀})
... | refl , refl | refl , refl = p , q
⊑ᶜ→⊑ (⊢↦ cwt dwt) ⊢idᶜ (⊑idL↦★ c≤id d≤id) = ⊑-★ , ⊑-★
⊑ᶜ→⊑ (⊢↦ cwt dwt) ⊢idᶜ (⊑idL↦ c≤id d≤id)
  with ⊑ᶜ→⊑ cwt ⊢idᶜ c≤id | ⊑ᶜ→⊑ dwt ⊢idᶜ d≤id
... | A⊑C , A⊑A′ | B⊑B′ , B⊑D = ⊑-⇒ A⊑A′ B⊑B′ , ⊑-⇒ A⊑C B⊑D
⊑ᶜ→⊑ (⊢⨟ cwt dwt) ⊢c′ (⊑idL⨟ p q)
  with ⊑ᶜ→⊑ cwt ⊢c′ p | ⊑ᶜ→⊑ dwt ⊢c′ q
... | A′⊑A , _ | _ , B′⊑B = A′⊑A , B′⊑B
⊑ᶜ→⊑ ⊢c ⊢c′ (⊑idR {A = A₀} atomic c p q)
  with coercion-type-unique ⊢c (⊢idᶜ {A = A₀}) | coercion-type-unique ⊢c′ c
... | refl , refl | refl , refl = p , q
⊑ᶜ→⊑ ⊢idᶜ (⊢↦ cwt dwt) (⊑idR↦ c≤id d≤id)
  with ⊑ᶜ→⊑ ⊢idᶜ cwt c≤id | ⊑ᶜ→⊑ ⊢idᶜ dwt d≤id
... | C⊑A , A′⊑A | B′⊑B , D⊑B = ⊑-⇒ A′⊑A B′⊑B , ⊑-⇒ C⊑A D⊑B
⊑ᶜ→⊑ ⊢c (⊢⨟ cwt dwt) (⊑idR⨟ p q)
  with ⊑ᶜ→⊑ ⊢c cwt p | ⊑ᶜ→⊑ ⊢c dwt q
... | A′⊑A , _ | _ , B′⊑B = A′⊑A , B′⊑B
⊑ᶜ→⊑ (⊢! g) (⊢! g′) (⊑! A′⊑A) = A′⊑A , ⊑-★
⊑ᶜ→⊑ (⊢? g) (⊢? g′) (⊑? A′⊑A) = ⊑-★ , A′⊑A
⊑ᶜ→⊑ (⊢↦ cwt dwt) (⊢↦ c′wt d′wt) (⊑↦ c′⊑c d′⊑d)
  with ⊑ᶜ→⊑ cwt c′wt c′⊑c | ⊑ᶜ→⊑ dwt d′wt d′⊑d
... | C′⊑C , A′⊑A | B′⊑B , D′⊑D =
  ⊑-⇒ A′⊑A B′⊑B , ⊑-⇒ C′⊑C D′⊑D
⊑ᶜ→⊑ (⊢⨟ cwt dwt) (⊢⨟ c′wt d′wt) (⊑⨟ c′⊑c d′⊑d)
  with ⊑ᶜ→⊑ cwt c′wt c′⊑c | ⊑ᶜ→⊑ dwt d′wt d′⊑d
... | A′⊑A , _ | _ , C′⊑C = A′⊑A , C′⊑C
⊑ᶜ→⊑ ⊢c (⊢⨟ (⊢? G-⇒) c′wt) (⊑drop? c′⊑c)
  with ⊑ᶜ→⊑ ⊢c c′wt c′⊑c
... | _ , B′⊑B = ⊑-★ , B′⊑B
⊑ᶜ→⊑ ⊢c (⊢⨟ c′wt (⊢! G-⇒)) (⊑drop! c′⊑c)
  with ⊑ᶜ→⊑ ⊢c c′wt c′⊑c
... | A′⊑A , _ = A′⊑A , ⊑-★

⊑idR↦-inv : ∀ {A B c d}
  → (c ↦ d) ⊑ᶜ idᶜ (A ⇒ B)
  → c ⊑ᶜ idᶜ A × d ⊑ᶜ idᶜ B
⊑idR↦-inv (⊑idR↦ c≤id d≤id) = c≤id , d≤id

