module Types where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Empty using (⊥; ⊥-elim)

data Ty : Set where
  ℕ   : Ty
  ★   : Ty
  _⇒_ : Ty → Ty → Ty
--  _×_ : Ty → Ty → Ty

data Ground : Ty → Set where
  G-ℕ : Ground ℕ
  G-⇒ : Ground (★ ⇒ ★)
--  G-× :  Ground (★ × ★)

------------------------------------------------------------
-- Type Consistency
------------------------------------------------------------

infix 4 _~_

data _~_ : Ty → Ty → Set where
  ~-ℕ  : ℕ ~ ℕ
  ~-★ : ★ ~ ★
  ★~ℕ : ★ ~ ℕ
  ℕ~★ : ℕ ~ ★
  ★~⇒ : ∀{A B}
    → A ~ ★
    → ★ ~ B
    → ★ ~ (A ⇒ B)
  ⇒~★ : ∀{A B}
    → ★ ~ A
    → B ~ ★
    → (A ⇒ B) ~ ★
  ~-⇒  : ∀ {A B C D}
    → C ~ A
    → B ~ D
    → (A ⇒ B) ~ (C ⇒ D)

~-sym : ∀ {A B}
  → A ~ B
  → B ~ A
~-sym ~-ℕ = ~-ℕ
~-sym ~-★ = ~-★
~-sym ★~ℕ = ℕ~★
~-sym ℕ~★ = ★~ℕ
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (~-⇒ C~A B~D) = ~-⇒ (~-sym C~A) (~-sym B~D)

~-refl : ∀ {A} → A ~ A
~-refl {A = ℕ} = ~-ℕ
~-refl {A = ★} = ~-★
~-refl {A = A ⇒ B} = ~-⇒ ~-refl ~-refl

mutual
  ★~-ty : ∀ A → ★ ~ A
  ★~-ty ℕ = ★~ℕ
  ★~-ty ★ = ~-★
  ★~-ty (A ⇒ B) = ★~⇒ (~★-ty A) (★~-ty B)

  ~★-ty : ∀ A → A ~ ★
  ~★-ty ℕ = ℕ~★
  ~★-ty ★ = ~-★
  ~★-ty (A ⇒ B) = ⇒~★ (★~-ty A) (~★-ty B)

------------------------------------------------------------
-- Type Precision
------------------------------------------------------------

infix 4 _⊑_
data _⊑_ : Ty → Ty → Set where
  ⊑-ℕ : ℕ ⊑ ℕ
  ⊑-★ : ∀ {A} → ★ ⊑ A
  ⊑-⇒ : ∀ {A B C D}
    → A ⊑ C
    → B ⊑ D
    → (A ⇒ B) ⊑ (C ⇒ D)

⊑-refl : ∀ {A} → A ⊑ A
⊑-refl {A = ℕ} = ⊑-ℕ
⊑-refl {A = ★} = ⊑-★
⊑-refl {A = A ⇒ B} = ⊑-⇒ ⊑-refl ⊑-refl

mutual
  prec-left : ∀ {X A B} → X ⊑ A → A ~ B → X ~ B
  prec-left ⊑-★ A~B = ★~-ty _
  prec-left ⊑-ℕ A~B = A~B
  prec-left (⊑-⇒ X⊑A₁ X₂⊑A₂) (⇒~★ ★~A₁ A₂~★) =
    ⇒~★ (★~-ty _) (prec-left X₂⊑A₂ A₂~★)
  prec-left (⊑-⇒ X⊑A₁ X₂⊑A₂) (~-⇒ B₁~A₁ A₂~B₂) =
    ~-⇒ (prec-right B₁~A₁ X⊑A₁) (prec-left X₂⊑A₂ A₂~B₂)

  prec-right : ∀ {A B Y} → A ~ B → Y ⊑ B → A ~ Y
  prec-right A~B ⊑-★ = ~★-ty _
  prec-right A~B ⊑-ℕ = A~B
  prec-right (★~⇒ B₁~★ ★~B₂) (⊑-⇒ Y⊑B₁ Y₂⊑B₂) =
    ★~⇒ (prec-left Y⊑B₁ B₁~★) (prec-right ★~B₂ Y₂⊑B₂)
  prec-right (~-⇒ B₁~A₁ A₂~B₂) (⊑-⇒ Y⊑B₁ Y₂⊑B₂) =
    ~-⇒ (prec-left Y⊑B₁ B₁~A₁) (prec-right A₂~B₂ Y₂⊑B₂)

app-consistency
  : ∀ {A B A′ B′ }
  → A′ ⊑ A
  → A ~ B
  → B′ ⊑ B
  → A′ ~ B′
app-consistency A′⊑A A~B B′⊑B = prec-left A′⊑A (prec-right A~B B′⊑B)

ground-upper-unique
  : ∀ {G H A}
  → Ground G
  → Ground H
  → G ⊑ A
  → H ⊑ A
  → G ≡ H
ground-upper-unique G-ℕ G-ℕ ⊑-ℕ ⊑-ℕ = refl
ground-upper-unique G-ℕ G-⇒ ⊑-ℕ ()
ground-upper-unique G-⇒ G-ℕ (⊑-⇒ _ _) ()
ground-upper-unique G-⇒ G-⇒ (⊑-⇒ _ _) (⊑-⇒ _ _) = refl

ground-not-⊑★ : ∀ {G} → Ground G → G ⊑ ★ → ⊥
ground-not-⊑★ G-ℕ ()
ground-not-⊑★ G-⇒ ()

ℕ-⊑-inv : ∀ {A} → ℕ ⊑ A → A ≡ ℕ
ℕ-⊑-inv ⊑-ℕ = refl

less-ground-not-★ : ∀ {G A}
  → Ground G
  → G ⊑ A
  → A ≢ ★
less-ground-not-★ G-ℕ () refl
less-ground-not-★ G-⇒ () refl
