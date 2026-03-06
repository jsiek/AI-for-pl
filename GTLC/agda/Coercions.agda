module Coercions where

open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import GTLC using
  ( Ty
  ; ℕ
  ; ★
  ; _⇒_
  ; _~_
  ; _⊑_
  ; ⊑-ℕ
  ; ⊑-★
  ; ⊑-⇒
  ; ⊑-refl
  ; ~-ℕ
  ; ~-★
  ; ★~ℕ
  ; ℕ~★
  ; ★~⇒
  ; ⇒~★
  ; ~-⇒
  )

infixr 7 _⨟_
infixr 6 _↦_

data Ground : Ty → Set where
  G-ℕ : Ground ℕ
  G-⇒ : Ground (★ ⇒ ★)

data Coercion : Set where
  idᶜ  : Ty → Coercion
  _!   : Ty → Coercion
  _`?  : Ty → Coercion
  _↦_  : Coercion → Coercion → Coercion
  _⨟_  : Coercion → Coercion → Coercion

data Seq : Coercion → Set where
  seq : ∀ {c d} → Seq (c ⨟ d)

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
  ⊑idᶜ : ∀ {A A′} → A′ ⊑ A → idᶜ A′ ⊑ᶜ idᶜ A
  ⊑idL  : ∀ {A B C c} → ¬ Seq c → ⊢ c ⦂ B ⇨ C → A ⊑ B → A ⊑ C → idᶜ A ⊑ᶜ c
  ⊑idL⨟ : ∀ {A c d} → idᶜ A ⊑ᶜ c → idᶜ A ⊑ᶜ d → idᶜ A ⊑ᶜ (c ⨟ d)
  ⊑idR  : ∀ {A B C c} → ¬ Seq c → ⊢ c ⦂ B ⇨ C → B ⊑ A → C ⊑ A → c ⊑ᶜ idᶜ A
  ⊑idR⨟ : ∀ {A c d} → c ⊑ᶜ idᶜ A → d ⊑ᶜ idᶜ A → (c ⨟ d) ⊑ᶜ idᶜ A
  ⊑!   : ∀ {A A′} → A′ ⊑ A → A′ ! ⊑ᶜ A !
  ⊑?   : ∀ {A A′} → A′ ⊑ A → A′ `? ⊑ᶜ A `?
  ⊑↦   : ∀ {c c′ d d′} → c′ ⊑ᶜ c → d′ ⊑ᶜ d → (c′ ↦ d′) ⊑ᶜ (c ↦ d)
  ⊑⨟   : ∀ {c c′ d d′} → c′ ⊑ᶜ c → d′ ⊑ᶜ d → (c′ ⨟ d′) ⊑ᶜ (c ⨟ d)
  ⊑drop? : ∀ {c c′} → c′ ⊑ᶜ c → ((★ ⇒ ★) `? ⨟ c′) ⊑ᶜ c
  ⊑drop! : ∀ {c c′} → c′ ⊑ᶜ c → (c′ ⨟ ((★ ⇒ ★) !)) ⊑ᶜ c

⊑ᶜ-reflexive : ∀ {c} → c ⊑ᶜ c
⊑ᶜ-reflexive {c = idᶜ A} = ⊑idᶜ ⊑-refl
⊑ᶜ-reflexive {c = A !} = ⊑! ⊑-refl
⊑ᶜ-reflexive {c = A `?} = ⊑? ⊑-refl
⊑ᶜ-reflexive {c = c ↦ d} = ⊑↦ ⊑ᶜ-reflexive ⊑ᶜ-reflexive
⊑ᶜ-reflexive {c = c ⨟ d} = ⊑⨟ ⊑ᶜ-reflexive ⊑ᶜ-reflexive

coerce-⊑ᶜ
  : ∀ {A A′ B B′}
  → A′ ⊑ A
  → (c : A ~ B)
  → B′ ⊑ B
  → (d : A′ ~ B′)
  → coerce d ⊑ᶜ coerce c
coerce-⊑ᶜ A′⊑A ~-ℕ B′⊑B ~-ℕ = ⊑idᶜ ⊑-ℕ
coerce-⊑ᶜ A′⊑A ~-ℕ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-⊑ᶜ A′⊑A ~-ℕ B′⊑B ★~ℕ = ⊑idR (λ ()) (⊢? G-ℕ) A′⊑A ⊑-refl
coerce-⊑ᶜ A′⊑A ~-ℕ B′⊑B ℕ~★ = ⊑idR (λ ()) (⊢! G-ℕ) A′⊑A ⊑-★
coerce-⊑ᶜ A′⊑A ~-★ B′⊑B ~-★ = ⊑idᶜ ⊑-★
coerce-⊑ᶜ A′⊑A ★~ℕ B′⊑B ~-★ = ⊑idL (λ ()) (⊢? G-ℕ) A′⊑A ⊑-★
coerce-⊑ᶜ A′⊑A ★~ℕ B′⊑B ★~ℕ = ⊑? ⊑-refl
coerce-⊑ᶜ A′⊑A ℕ~★ B′⊑B ~-★ = ⊑idL (λ ()) (⊢! G-ℕ) A′⊑A ⊑-★
coerce-⊑ᶜ A′⊑A ℕ~★ B′⊑B ℕ~★ = ⊑! ⊑-refl
coerce-⊑ᶜ A′⊑A (★~⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟ (⊑idL (λ ()) (⊢? G-⇒) A′⊑A ⊑-★)
        (⊑idL (λ ()) (⊢↦ (coerce-wt c₁) (coerce-wt c₂)) ⊑-★ ⊑-★)
coerce-⊑ᶜ A′⊑A (★~⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑⨟
    (⊑? ⊑-refl)
    (⊑↦
      (coerce-⊑ᶜ B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-⊑ᶜ ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-⊑ᶜ A′⊑A (⇒~★ c₁ c₂) B′⊑B ~-★ =
  ⊑idL⨟ (⊑idL (λ ()) (⊢↦ (coerce-wt c₁) (coerce-wt c₂)) ⊑-★ ⊑-★)
        (⊑idL (λ ()) (⊢! G-⇒) ⊑-★ ⊑-★) 
coerce-⊑ᶜ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (⇒~★ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑⨟
    (⊑↦
      (coerce-⊑ᶜ ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-⊑ᶜ A′₂⊑A₂ c₂ ⊑-★ d₂))
    (⊑! ⊑-refl)
coerce-⊑ᶜ A′⊑A (~-⇒ c₁ c₂) B′⊑B ~-★ =
  ⊑idL (λ ()) (⊢↦ (coerce-wt c₁) (coerce-wt c₂)) ⊑-★ ⊑-★
coerce-⊑ᶜ A′⊑A (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (★~⇒ d₁ d₂) =
  ⊑drop?
    (⊑↦
      (coerce-⊑ᶜ B′₁⊑B₁ c₁ ⊑-★ d₁)
      (coerce-⊑ᶜ ⊑-★ c₂ B′₂⊑B₂ d₂))
coerce-⊑ᶜ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) B′⊑B (⇒~★ d₁ d₂) =
  ⊑drop!
    (⊑↦
      (coerce-⊑ᶜ ⊑-★ c₁ A′₁⊑A₁ d₁)
      (coerce-⊑ᶜ A′₂⊑A₂ c₂ ⊑-★ d₂))
coerce-⊑ᶜ (⊑-⇒ A′₁⊑A₁ A′₂⊑A₂) (~-⇒ c₁ c₂) (⊑-⇒ B′₁⊑B₁ B′₂⊑B₂) (~-⇒ d₁ d₂) =
  ⊑↦
    (coerce-⊑ᶜ B′₁⊑B₁ c₁ A′₁⊑A₁ d₁)
    (coerce-⊑ᶜ A′₂⊑A₂ c₂ B′₂⊑B₂ d₂)

coercion-type-unique : ∀ {c A B C D} → ⊢ c ⦂ A ⇨ B → ⊢ c ⦂ C ⇨ D → A ≡ C × B ≡ D
coercion-type-unique ⊢idᶜ ⊢idᶜ = refl , refl
coercion-type-unique (⊢! g₁) (⊢! g₂) = refl , refl
coercion-type-unique (⊢? g₁) (⊢? g₂) = refl , refl
coercion-type-unique (⊢↦ c₁ d₁) (⊢↦ c₂ d₂)
  with coercion-type-unique c₁ c₂ | coercion-type-unique d₁ d₂
... | refl , refl | refl , refl = refl , refl
coercion-type-unique (⊢⨟ c₁ d₁) (⊢⨟ c₂ d₂)
  with coercion-type-unique c₁ c₂ | coercion-type-unique d₁ d₂
... | refl , refl | refl , refl = refl , refl

⊑ᶜ→⊑ : ∀ {c c′ A B A′ B′ } → ⊢ c ⦂ A ⇨ B → ⊢ c′ ⦂ A′ ⇨ B′
    → c′ ⊑ᶜ c → A′ ⊑ A × B′ ⊑ B
⊑ᶜ→⊑ ⊢idᶜ ⊢idᶜ (⊑idᶜ A′⊑A) = A′⊑A , A′⊑A
⊑ᶜ→⊑ ⊢c ⊢c′ (⊑idL {A = A₀} nseq c p q)
  with coercion-type-unique ⊢c c | coercion-type-unique ⊢c′ (⊢idᶜ {A = A₀})
... | refl , refl | refl , refl = p , q
⊑ᶜ→⊑ (⊢⨟ cwt dwt) ⊢c′ (⊑idL⨟ p q)
  with ⊑ᶜ→⊑ cwt ⊢c′ p | ⊑ᶜ→⊑ dwt ⊢c′ q
... | A′⊑A , _ | _ , B′⊑B = A′⊑A , B′⊑B
⊑ᶜ→⊑ ⊢c ⊢c′ (⊑idR {A = A₀} nseq c p q)
  with coercion-type-unique ⊢c (⊢idᶜ {A = A₀}) | coercion-type-unique ⊢c′ c
... | refl , refl | refl , refl = p , q
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
