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

  ⊑⊥ : ∀{c}{A}{B}{A′}{B′}
    → ⊢ c ⦂ A′ ⇨ B′
    → A′ ⊑ A
    → B′ ⊑ B
    → c ⊑ᶜ ⊥ᶜ A ⇨ B

⊑ᶜ-reflexive : ∀ {c} → c ⊑ᶜ c
⊑ᶜ-reflexive {c = idᶜ A} = ⊑idᶜ ⊑-refl
⊑ᶜ-reflexive {c = A !} = ⊑! ⊑-refl
⊑ᶜ-reflexive {c = A `?} = ⊑? ⊑-refl
⊑ᶜ-reflexive {c = c ↦ d} = ⊑↦ ⊑ᶜ-reflexive ⊑ᶜ-reflexive
⊑ᶜ-reflexive {c = c ⨟ d} = ⊑⨟ ⊑ᶜ-reflexive ⊑ᶜ-reflexive
⊑ᶜ-reflexive {c = ⊥ᶜ A ⇨ B} = ⊑⊥ ⊢⊥ ⊑-refl ⊑-refl

⊑id★ : ∀ {c A B} → ⊢ c ⦂ A ⇨ B → idᶜ ★ ⊑ᶜ c
⊑id★ ⊢idᶜ = ⊑idᶜ ⊑-★
⊑id★ (⊢! g) = ⊑idL atom-! (⊢! g) ⊑-★ ⊑-★
⊑id★ (⊢? g) = ⊑idL atom-? (⊢? g) ⊑-★ ⊑-★
⊑id★ (⊢↦ cwt dwt) = ⊑idL↦★ (⊑id★ cwt) (⊑id★ dwt)
⊑id★ (⊢⨟ cwt dwt) = ⊑idL⨟ (⊑id★ cwt) (⊑id★ dwt)
⊑id★ (⊢⊥{A}{B}) = ⊑⊥ ⊢idᶜ ⊑-★ ⊑-★

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
coercion-type-unique ⊢⊥ ⊢⊥ = refl , refl

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
⊑ᶜ→⊑ ⊢⊥ c′wt (⊑⊥ c′wt′ A′⊑A B′⊑B)
  with coercion-type-unique c′wt c′wt′
... | refl , refl = A′⊑A , B′⊑B
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


{-# TERMINATING #-}
normalize-seqᶜ : ∀ {c d A B C}
  → ⊢ c ⦂ A ⇨ B
  → ⊢ d ⦂ B ⇨ C
  → Normalᶜ c
  → Normalᶜ d
  → ∃[ e ] ((c ⨟ d) —↠ᶜᶜ e) × Normalᶜ e

normalizeᶜ : ∀ {c A B}
  → ⊢ c ⦂ A ⇨ B
  → ∃[ c′ ] (c —↠ᶜᶜ c′) × Normalᶜ c′
normalizeᶜ {c = idᶜ A} ⊢idᶜ =
  (idᶜ A) , ((idᶜ A ∎ᶜᶜ) , nf-id)
normalizeᶜ {c = G !} (⊢! g) =
  (G !) , ((G ! ∎ᶜᶜ) , nf-! g)
normalizeᶜ {c = G `?} (⊢? g) =
  (G `?) , ((G `? ∎ᶜᶜ) , nf-? g)
normalizeᶜ {c = c ↦ d} (⊢↦ cwt dwt)
  with normalizeᶜ cwt | normalizeᶜ dwt
... | c′ , c↠c′ , nfc | d′ , d↠d′ , nfd =
  (c′ ↦ d′)
  , (((c ↦ d)
    —↠ᶜᶜ⟨ multi-ξ-↦₁ᶜᶜ c↠c′ ⟩
    (c′ ↦ d)
    —↠ᶜᶜ⟨ multi-ξ-↦₂ᶜᶜ d↠d′ ⟩
    (c′ ↦ d′)
    ∎ᶜᶜ)
    , nf-↦ nfc nfd)
normalizeᶜ {c = c ⨟ d} (⊢⨟ cwt dwt)
  with normalizeᶜ cwt | normalizeᶜ dwt
... | c′ , c↠c′ , nfc | d′ , d↠d′ , nfd
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ cwt c↠c′)
    (preserve-—↠ᶜᶜ dwt d↠d′)
    nfc nfd
... | e , c′⨟d′↠e , nfe =
  e
  , (((c ⨟ d)
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c↠c′ ⟩
    (c′ ⨟ d)
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ d↠d′ ⟩
    (c′ ⨟ d′)
    —↠ᶜᶜ⟨ c′⨟d′↠e ⟩
    e
    ∎ᶜᶜ)
    , nfe)
normalizeᶜ {c = ⊥ᶜ A ⇨ B} ⊢⊥ =
  (⊥ᶜ A ⇨ B) , (((⊥ᶜ A ⇨ B) ∎ᶜᶜ) , nf-⊥)

-- Left sequence forms: reassociate right and normalize inside first.
normalize-seqᶜ
  {c = (G `? ⨟ (c₁ ↦ c₂))} {d = d}
  (⊢⨟ (⊢? g) (⊢↦ c₁wt c₂wt)) dwt (nf-?↦ _ n₁ n₂) nd
  with normalize-seqᶜ (⊢↦ c₁wt c₂wt) dwt (nf-↦ n₁ n₂) nd
... | x , arr⨟d↠x , nfx
  with normalize-seqᶜ (⊢? g)
    (preserve-—↠ᶜᶜ (⊢⨟ (⊢↦ c₁wt c₂wt) dwt) arr⨟d↠x)
    (nf-? g) nfx
... | e , ?⨟x↠e , nfe =
  e , ((((G `? ⨟ (c₁ ↦ c₂)) ⨟ d)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    (G `? ⨟ ((c₁ ↦ c₂) ⨟ d))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ arr⨟d↠x ⟩
    (G `? ⨟ x)
    —↠ᶜᶜ⟨ ?⨟x↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = ((c₁ ↦ c₂) ⨟ (G !))} {d = d}
  (⊢⨟ (⊢↦ c₁wt c₂wt) (⊢! g)) dwt (nf-↦! n₁ n₂ _) nd
  with normalize-seqᶜ (⊢! g) dwt (nf-! g) nd
... | x , !⨟d↠x , nfx
  with normalize-seqᶜ (⊢↦ c₁wt c₂wt)
    (preserve-—↠ᶜᶜ (⊢⨟ (⊢! g) dwt) !⨟d↠x)
    (nf-↦ n₁ n₂) nfx
... | e , ↦⨟x↠e , nfe =
  e , (((((c₁ ↦ c₂) ⨟ (G !)) ⨟ d)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    ((c₁ ↦ c₂) ⨟ ((G !) ⨟ d))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ !⨟d↠x ⟩
    ((c₁ ↦ c₂) ⨟ x)
    —↠ᶜᶜ⟨ ↦⨟x↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = ((G `? ⨟ (c₁ ↦ c₂)) ⨟ (G !))} {d = d}
  (⊢⨟ (⊢⨟ (⊢? g) (⊢↦ c₁wt c₂wt)) (⊢! g′)) dwt (nf-?↦! _ n₁ n₂) nd
  with normalize-seqᶜ (⊢! g′) dwt (nf-! g′) nd
... | x , !⨟d↠x , nfx
  with normalize-seqᶜ (⊢⨟ (⊢? g) (⊢↦ c₁wt c₂wt))
    (preserve-—↠ᶜᶜ (⊢⨟ (⊢! g′) dwt) !⨟d↠x)
    (nf-?↦ g n₁ n₂) nfx
... | e , ?↦⨟x↠e , nfe =
  e , (((((G `? ⨟ (c₁ ↦ c₂)) ⨟ (G !)) ⨟ d)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    ((G `? ⨟ (c₁ ↦ c₂)) ⨟ ((G !) ⨟ d))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ !⨟d↠x ⟩
    ((G `? ⨟ (c₁ ↦ c₂)) ⨟ x)
    —↠ᶜᶜ⟨ ?↦⨟x↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = (G `? ⨟ (⊥ᶜ A ⇨ B))} {d = d}
  (⊢⨟ (⊢? g) ⊢⊥) dwt (nf-?⊥ _) nd
  with normalize-seqᶜ ⊢⊥ dwt nf-⊥ nd
... | x , ⊥⨟d↠x , nfx
  with normalize-seqᶜ (⊢? g)
    (preserve-—↠ᶜᶜ (⊢⨟ ⊢⊥ dwt) ⊥⨟d↠x)
    (nf-? g) nfx
... | e , ?⨟x↠e , nfe =
  e , ((((G `? ⨟ (⊥ᶜ A ⇨ B)) ⨟ d)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    (G `? ⨟ ((⊥ᶜ A ⇨ B) ⨟ d))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ ⊥⨟d↠x ⟩
    (G `? ⨟ x)
    —↠ᶜᶜ⟨ ?⨟x↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = ((G `?) ⨟ (G !))} {d = d}
  (⊢⨟ (⊢? g) (⊢! g′)) dwt (nf-?! _) nd
  with normalize-seqᶜ (⊢! g′) dwt (nf-! g′) nd
... | x , !⨟d↠x , nfx
  with normalize-seqᶜ (⊢? g)
    (preserve-—↠ᶜᶜ (⊢⨟ (⊢! g′) dwt) !⨟d↠x)
    (nf-? g) nfx
... | e , ?⨟x↠e , nfe =
  e , ((((G `? ⨟ (G !)) ⨟ d)
    —→ᶜᶜ⟨ β-assocRᶜ ⟩
    (G `? ⨟ ((G !) ⨟ d))
    —↠ᶜᶜ⟨ multi-ξ-⨟₂ᶜᶜ !⨟d↠x ⟩
    (G `? ⨟ x)
    —↠ᶜᶜ⟨ ?⨟x↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

-- Right sequence forms: reassociate left and normalize inside first.
normalize-seqᶜ
  {c = c} {d = (G `? ⨟ (d₁ ↦ d₂))}
  cwt (⊢⨟ (⊢? g) (⊢↦ d₁wt d₂wt)) nc (nf-?↦ _ n₁ n₂)
  with normalize-seqᶜ cwt (⊢? g) nc (nf-? g)
... | x , c⨟?↠x , nfx
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ (⊢⨟ cwt (⊢? g)) c⨟?↠x)
    (⊢↦ d₁wt d₂wt) nfx (nf-↦ n₁ n₂)
... | e , x⨟↦↠e , nfe =
  e , (((c ⨟ (G `? ⨟ (d₁ ↦ d₂)))
    —→ᶜᶜ⟨ β-assocLᶜ ⟩
    ((c ⨟ (G `?)) ⨟ (d₁ ↦ d₂))
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c⨟?↠x ⟩
    (x ⨟ (d₁ ↦ d₂))
    —↠ᶜᶜ⟨ x⨟↦↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = c} {d = ((d₁ ↦ d₂) ⨟ (G !))}
  cwt (⊢⨟ (⊢↦ d₁wt d₂wt) (⊢! g)) nc (nf-↦! n₁ n₂ _)
  with normalize-seqᶜ cwt (⊢↦ d₁wt d₂wt) nc (nf-↦ n₁ n₂)
... | x , c⨟↦↠x , nfx
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ (⊢⨟ cwt (⊢↦ d₁wt d₂wt)) c⨟↦↠x)
    (⊢! g) nfx (nf-! g)
... | e , x⨟!↠e , nfe =
  e , (((c ⨟ ((d₁ ↦ d₂) ⨟ (G !)))
    —→ᶜᶜ⟨ β-assocLᶜ ⟩
    ((c ⨟ (d₁ ↦ d₂)) ⨟ (G !))
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c⨟↦↠x ⟩
    (x ⨟ (G !))
    —↠ᶜᶜ⟨ x⨟!↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = c} {d = ((G `? ⨟ (d₁ ↦ d₂)) ⨟ (G !))}
  cwt (⊢⨟ (⊢⨟ (⊢? g) (⊢↦ d₁wt d₂wt)) (⊢! g′)) nc (nf-?↦! _ n₁ n₂)
  with normalize-seqᶜ cwt (⊢⨟ (⊢? g) (⊢↦ d₁wt d₂wt)) nc (nf-?↦ g n₁ n₂)
... | x , c⨟?↦↠x , nfx
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ (⊢⨟ cwt (⊢⨟ (⊢? g) (⊢↦ d₁wt d₂wt))) c⨟?↦↠x)
    (⊢! g′) nfx (nf-! g′)
... | e , x⨟!↠e , nfe =
  e , (((c ⨟ ((G `? ⨟ (d₁ ↦ d₂)) ⨟ (G !)))
    —→ᶜᶜ⟨ β-assocLᶜ ⟩
    ((c ⨟ (G `? ⨟ (d₁ ↦ d₂))) ⨟ (G !))
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c⨟?↦↠x ⟩
    (x ⨟ (G !))
    —↠ᶜᶜ⟨ x⨟!↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = c} {d = (G `? ⨟ (⊥ᶜ A ⇨ B))}
  cwt (⊢⨟ (⊢? g) ⊢⊥) nc (nf-?⊥ _)
  with normalize-seqᶜ cwt (⊢? g) nc (nf-? g)
... | x , c⨟?↠x , nfx
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ (⊢⨟ cwt (⊢? g)) c⨟?↠x)
    ⊢⊥ nfx nf-⊥
... | e , x⨟⊥↠e , nfe =
  e , (((c ⨟ (G `? ⨟ (⊥ᶜ A ⇨ B)))
    —→ᶜᶜ⟨ β-assocLᶜ ⟩
    ((c ⨟ (G `?)) ⨟ (⊥ᶜ A ⇨ B))
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c⨟?↠x ⟩
    (x ⨟ (⊥ᶜ A ⇨ B))
    —↠ᶜᶜ⟨ x⨟⊥↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

normalize-seqᶜ
  {c = c} {d = ((G `?) ⨟ (G !))}
  cwt (⊢⨟ (⊢? g) (⊢! g′)) nc (nf-?! _)
  with normalize-seqᶜ cwt (⊢? g) nc (nf-? g)
... | x , c⨟?↠x , nfx
  with normalize-seqᶜ
    (preserve-—↠ᶜᶜ (⊢⨟ cwt (⊢? g)) c⨟?↠x)
    (⊢! g′) nfx (nf-! g′)
... | e , x⨟!↠e , nfe =
  e , (((c ⨟ ((G `?) ⨟ (G !)))
    —→ᶜᶜ⟨ β-assocLᶜ ⟩
    ((c ⨟ (G `?)) ⨟ (G !))
    —↠ᶜᶜ⟨ multi-ξ-⨟₁ᶜᶜ c⨟?↠x ⟩
    (x ⨟ (G !))
    —↠ᶜᶜ⟨ x⨟!↠e ⟩
    e
    ∎ᶜᶜ) , nfe)

-- Impossible: projections cannot have codomain ★.
normalize-seqᶜ {c = (G `?)} {B = ★} (⊢? ()) dwt nfc nfd

-- Base cases (no sequence constructor on either side).
normalize-seqᶜ {c = idᶜ A} {d = d} ⊢idᶜ dwt nf-id nd =
  d , ((((idᶜ A) ⨟ d)
    —→ᶜᶜ⟨ β-idLᶜ ⟩
    d
    ∎ᶜᶜ) , nd)

normalize-seqᶜ {c = c} {d = idᶜ B} cwt ⊢idᶜ nc nf-id =
  c , (((c ⨟ (idᶜ B))
    —→ᶜᶜ⟨ β-idRᶜ ⟩
    c
    ∎ᶜᶜ) , nc)

normalize-seqᶜ {c = (⊥ᶜ A ⇨ B)} {d = d} ⊢⊥ dwt nf-⊥ nd =
  (⊥ᶜ A ⇨ _) , ((((⊥ᶜ A ⇨ B) ⨟ d)
    —→ᶜᶜ⟨ β-⊥Lᶜ dwt ⟩
    (⊥ᶜ A ⇨ _)
    ∎ᶜᶜ) , nf-⊥)

normalize-seqᶜ {c = (G !)} {d = (H `?)} (⊢! g) (⊢? h) (nf-! _) (nf-? _)
  with g | h
... | G-ℕ | G-ℕ =
  (idᶜ ℕ) , ((((ℕ !) ⨟ (ℕ `?))
    —→ᶜᶜ⟨ β-proj-inj-okᶜ ⟩
    idᶜ ℕ
    ∎ᶜᶜ) , nf-id)
... | G-ℕ | G-⇒ =
  (⊥ᶜ ℕ ⇨ (★ ⇒ ★)) , ((((ℕ !) ⨟ ((★ ⇒ ★) `?))
    —→ᶜᶜ⟨ β-proj-inj-badᶜ (λ ()) ⟩
    (⊥ᶜ ℕ ⇨ (★ ⇒ ★))
    ∎ᶜᶜ) , nf-⊥)
... | G-⇒ | G-ℕ =
  (⊥ᶜ (★ ⇒ ★) ⇨ ℕ) , (((((★ ⇒ ★) !) ⨟ (ℕ `?))
    —→ᶜᶜ⟨ β-proj-inj-badᶜ (λ ()) ⟩
    (⊥ᶜ (★ ⇒ ★) ⇨ ℕ)
    ∎ᶜᶜ) , nf-⊥)
... | G-⇒ | G-⇒ =
  (idᶜ (★ ⇒ ★)) , (((((★ ⇒ ★) !) ⨟ ((★ ⇒ ★) `?))
    —→ᶜᶜ⟨ β-proj-inj-okᶜ ⟩
    idᶜ (★ ⇒ ★)
    ∎ᶜᶜ) , nf-id)

normalize-seqᶜ {c = (G !)} {d = (⊥ᶜ ★ ⇨ B)} (⊢! g) ⊢⊥ (nf-! _) nf-⊥ =
  (⊥ᶜ G ⇨ B) , ((((G !) ⨟ (⊥ᶜ ★ ⇨ B))
    —→ᶜᶜ⟨ β-!⊥ᶜ ⟩
    (⊥ᶜ G ⇨ B)
    ∎ᶜᶜ) , nf-⊥)

normalize-seqᶜ {c = (G `?)} {d = (G !)} (⊢? g) (⊢! _) (nf-? _) (nf-! _) =
  ((G `?) ⨟ (G !)) , ((((G `?) ⨟ (G !)) ∎ᶜᶜ) , nf-?! g)

normalize-seqᶜ {c = (G `?)} {d = (c₁ ↦ c₂)}
  (⊢? g) (⊢↦ c₁wt c₂wt) (nf-? _) (nf-↦ n₁ n₂) =
  ((G `?) ⨟ (c₁ ↦ c₂)) , ((((G `?) ⨟ (c₁ ↦ c₂)) ∎ᶜᶜ) , nf-?↦ g n₁ n₂)

normalize-seqᶜ {c = (G `?)} {d = (⊥ᶜ A ⇨ B)}
  (⊢? g) ⊢⊥ (nf-? _) nf-⊥ =
  ((G `?) ⨟ (⊥ᶜ A ⇨ B)) , ((((G `?) ⨟ (⊥ᶜ A ⇨ B)) ∎ᶜᶜ) , nf-?⊥ g)

normalize-seqᶜ {c = (c₁ ↦ c₂)} {d = (d₁ ↦ d₂)}
  (⊢↦ c₁wt c₂wt) (⊢↦ d₁wt d₂wt) (nf-↦ n₁ n₂) (nf-↦ n₃ n₄)
  with normalize-seqᶜ d₁wt c₁wt n₃ n₁
... | lc , d₁⨟c₁↠lc , nflc
  with normalize-seqᶜ c₂wt d₂wt n₂ n₄
... | rd , c₂⨟d₂↠rd , nfrd =
  (lc ↦ rd)
  , ((((c₁ ↦ c₂) ⨟ (d₁ ↦ d₂))
    —→ᶜᶜ⟨ β-↦ᶜ ⟩
    ((d₁ ⨟ c₁) ↦ (c₂ ⨟ d₂))
    —↠ᶜᶜ⟨ multi-ξ-↦₁ᶜᶜ d₁⨟c₁↠lc ⟩
    (lc ↦ (c₂ ⨟ d₂))
    —↠ᶜᶜ⟨ multi-ξ-↦₂ᶜᶜ c₂⨟d₂↠rd ⟩
    (lc ↦ rd)
    ∎ᶜᶜ) , nf-↦ nflc nfrd)

normalize-seqᶜ {c = (c₁ ↦ c₂)} {d = (G !)}
  (⊢↦ c₁wt c₂wt) (⊢! g) (nf-↦ n₁ n₂) (nf-! _) =
  ((c₁ ↦ c₂) ⨟ (G !)) , ((((c₁ ↦ c₂) ⨟ (G !)) ∎ᶜᶜ) , nf-↦! n₁ n₂ g)

normalize-seqᶜ {c = (c₁ ↦ c₂)} {d = (⊥ᶜ (C ⇒ D) ⇨ E)}
  (⊢↦ c₁wt c₂wt) ⊢⊥ (nf-↦ n₁ n₂) nf-⊥ =
  (⊥ᶜ _ ⇨ E) , ((((c₁ ↦ c₂) ⨟ (⊥ᶜ (C ⇒ D) ⇨ E))
    —→ᶜᶜ⟨ β-↦⊥ᶜ c₁wt c₂wt ⟩
    (⊥ᶜ _ ⇨ E)
    ∎ᶜᶜ) , nf-⊥)
