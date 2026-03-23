module Coercions where

open import Agda.Builtin.Nat using (Nat)
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
  _`?  : {ℓ : Nat} → Ty → Coercion -- projection (tag checking)
  _↦_  : Coercion → Coercion → Coercion
  _⨟_  : Coercion → Coercion → Coercion

data Atomic : Coercion → Set where
  atom-idᶜ : ∀ {A} → Atomic (idᶜ A)
  atom-! : ∀ {G} → Atomic (G !)
  atom-? : ∀ {G ℓ} → Atomic ((_`? {ℓ = ℓ}) G)

infix 4 ⊢_⦂_⇨_

data ⊢_⦂_⇨_ : Coercion → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → Ground G
    → ⊢ G ! ⦂ G ⇨ ★

  ⊢? : ∀ {G ℓ}
    → Ground G
    → ⊢ ((_`? {ℓ = ℓ}) G) ⦂ ★ ⇨ G

  ⊢↦ : ∀ {A B C D c d}
    → ⊢ c ⦂ C ⇨ A
    → ⊢ d ⦂ B ⇨ D
    → ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (C ⇒ D)

  ⊢⨟ : ∀ {A B C c d}
    → ⊢ c ⦂ A ⇨ B
    → ⊢ d ⦂ B ⇨ C
    → ⊢ c ⨟ d ⦂ A ⇨ C

coerce : ∀ {A B} → Nat → A ~ B → Coercion
coerce ℓ ~-ℕ = idᶜ ℕ
coerce ℓ ~-★ = idᶜ ★
coerce ℓ ★~ℕ = (_`? {ℓ = ℓ}) ℕ
coerce ℓ ℕ~★ = ℕ !
coerce ℓ (★~⇒ c d) = ((_`? {ℓ = ℓ}) (★ ⇒ ★)) ⨟ (coerce ℓ c ↦ coerce ℓ d)
coerce ℓ (⇒~★ c d) = (coerce ℓ c ↦ coerce ℓ d) ⨟ ((★ ⇒ ★) !)
coerce ℓ (~-⇒ c d) = coerce ℓ c ↦ coerce ℓ d

coerce-wt : ∀ {A B} (ℓ : Nat) (p : A ~ B) → ⊢ coerce ℓ p ⦂ A ⇨ B
coerce-wt ℓ ~-ℕ = ⊢idᶜ
coerce-wt ℓ ~-★ = ⊢idᶜ
coerce-wt ℓ ★~ℕ = ⊢? G-ℕ
coerce-wt ℓ ℕ~★ = ⊢! G-ℕ
coerce-wt ℓ (★~⇒ c d) =
  ⊢⨟ (⊢? G-⇒) (⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d))
coerce-wt ℓ (⇒~★ c d) =
  ⊢⨟ (⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d)) (⊢! G-⇒)
coerce-wt ℓ (~-⇒ c d) = ⊢↦ (coerce-wt ℓ c) (coerce-wt ℓ d)

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
  ⊑?   : ∀ {A A′ ℓ} → A′ ⊑ A
     → ((_`? {ℓ = ℓ}) A′) ⊑ᶜ ((_`? {ℓ = ℓ}) A)
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
  
  ⊑drop? : ∀ {c c′ ℓ}
    → c′ ⊑ᶜ c
    → (((_`? {ℓ = ℓ}) (★ ⇒ ★)) ⨟ c′) ⊑ᶜ c
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
  → (ℓ : Nat)
  → A′ ⊑ A
  → (c : A ~ B)
  → B′ ⊑ B
  → (d : A′ ~ B′)
  → coerce ℓ d ⊑ᶜ coerce ℓ c
coerce-monotonic ℓ A′⊑A ~-ℕ B′⊑B ~-ℕ = ⊑idᶜ ⊑-ℕ
coerce-monotonic ℓ A′⊑A ~-ℕ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-monotonic ℓ A′⊑A ~-ℕ B′⊑B ★~ℕ = ⊑idR atom-? (⊢? G-ℕ) A′⊑A ⊑-refl
coerce-monotonic ℓ A′⊑A ~-ℕ B′⊑B ℕ~★ = ⊑idR atom-! (⊢! G-ℕ) A′⊑A ⊑-★
coerce-monotonic ℓ A′⊑A ~-★ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-monotonic ℓ A′⊑A ★~ℕ B′⊑B ~-★ = ⊑idL atom-? (⊢? G-ℕ) A′⊑A ⊑-★
coerce-monotonic ℓ A′⊑A ★~ℕ B′⊑B ★~ℕ = ⊑? ⊑-refl
coerce-monotonic ℓ A′⊑A ℕ~★ B′⊑B ~-★ = ⊑idL atom-! (⊢! G-ℕ) A′⊑A ⊑-★
coerce-monotonic ℓ A′⊑A ℕ~★ B′⊑B ℕ~★ = ⊑! ⊑-refl
coerce-monotonic ℓ A′⊑A (★~⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟ (⊑idL atom-? (⊢? G-⇒) A′⊑A ⊑-★)
        (⊑idL↦★
          (⊑id★ (coerce-wt ℓ c₁))
          (⊑id★ (coerce-wt ℓ c₂)))
coerce-monotonic ℓ A′⊑A (★~⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑⨟
    (⊑? ⊑-refl)
    (⊑↦
      (coerce-monotonic ℓ B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-monotonic ℓ ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-monotonic ℓ A′⊑A (⇒~★ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟
        (⊑idL↦★
          (⊑id★ (coerce-wt ℓ c₁))
          (⊑id★ (coerce-wt ℓ c₂)))
        (⊑idL atom-! (⊢! G-⇒) ⊑-★ ⊑-★)
coerce-monotonic ℓ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (⇒~★ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑⨟
    (⊑↦
      (coerce-monotonic ℓ ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-monotonic ℓ A′₂⊑A₂ c₂ ⊑-★ d₂))
    (⊑! ⊑-refl)
coerce-monotonic ℓ A′⊑A (~-⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL↦★
    (⊑id★ (coerce-wt ℓ c₁))
    (⊑id★ (coerce-wt ℓ c₂))
coerce-monotonic ℓ A′⊑A (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑drop?
    (⊑↦
      (coerce-monotonic ℓ B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-monotonic ℓ ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-monotonic ℓ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑drop!
    (⊑↦
      (coerce-monotonic ℓ ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-monotonic ℓ A′₂⊑A₂ c₂ ⊑-★ d₂))
coerce-monotonic ℓ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (~-⇒ d₁ d₂) =
  ⊑↦
    (coerce-monotonic ℓ B′₁⊑B₁ c₁ A′₁⊑A₁ d₁)
    (coerce-monotonic ℓ A′₂⊑A₂ c₂ B′₂⊑B₂ d₂)

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
