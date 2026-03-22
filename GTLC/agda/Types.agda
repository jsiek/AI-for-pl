module Types where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Nullary using (Dec; yes; no; ¬_)

data Ty : Set where
  ℕ   : Ty
  ★   : Ty
  _⇒_ : Ty → Ty → Ty
--  _×_ : Ty → Ty → Ty

data Ground : Ty → Set where
  G-ℕ : Ground ℕ
  G-⇒ : Ground (★ ⇒ ★)

ground-irrelevant : ∀ {G} → (g g′ : Ground G) → g ≡ g′
ground-irrelevant G-ℕ G-ℕ = refl
ground-irrelevant G-⇒ G-⇒ = refl

_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
ℕ ≟Ty ℕ = yes refl
ℕ ≟Ty ★ = no (λ ())
ℕ ≟Ty (B ⇒ C) = no (λ ())
★ ≟Ty ℕ = no (λ ())
★ ≟Ty ★ = yes refl
★ ≟Ty (B ⇒ C) = no (λ ())
(A ⇒ B) ≟Ty ℕ = no (λ ())
(A ⇒ B) ≟Ty ★ = no (λ ())
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no A≢C | _ = no (λ { refl → A≢C refl })
... | _ | no B≢D = no (λ { refl → B≢D refl })

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

⊑-trans : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
⊑-trans ⊑-★ B⊑C = ⊑-★
⊑-trans ⊑-ℕ ⊑-ℕ = ⊑-ℕ
⊑-trans (⊑-⇒ A⊑B B⊑D) (⊑-⇒ B⊑C D⊑E) =
  ⊑-⇒ (⊑-trans A⊑B B⊑C) (⊑-trans B⊑D D⊑E)

upper-bounds-consistent : ∀ {A B C} → A ⊑ C → B ⊑ C → A ~ B
upper-bounds-consistent (⊑-★ {A}) pB = ★~-ty _
upper-bounds-consistent ⊑-ℕ ⊑-ℕ = ~-ℕ
upper-bounds-consistent ⊑-ℕ ⊑-★ = ℕ~★
upper-bounds-consistent (⊑-⇒ A⊑C B⊑D) ⊑-★ = ~★-ty _
upper-bounds-consistent (⊑-⇒ A⊑C B⊑D) (⊑-⇒ A′⊑C B′⊑D) =
  ~-⇒
    (upper-bounds-consistent A′⊑C A⊑C)
    (upper-bounds-consistent B⊑D B′⊑D)

Lub : Ty → Ty → Ty → Set
Lub A B C =
  (A ⊑ C) × ((B ⊑ C) × (∀ {D} → A ⊑ D → B ⊑ D → C ⊑ D))

mkLub :
  ∀ {A B C} →
  A ⊑ C →
  B ⊑ C →
  (∀ {D} → A ⊑ D → B ⊑ D → C ⊑ D) →
  Lub A B C
mkLub A⊑C B⊑C least = A⊑C , (B⊑C , least)

consistency→lub : ∀ {A B} → A ~ B → Σ Ty (Lub A B)
consistency→lub ~-ℕ =
  ℕ , mkLub ⊑-ℕ ⊑-ℕ (λ A⊑D B⊑D → A⊑D)
consistency→lub ~-★ =
  ★ , mkLub ⊑-★ ⊑-★ (λ A⊑D B⊑D → A⊑D)
consistency→lub ★~ℕ =
  ℕ , mkLub ⊑-★ ⊑-ℕ (λ A⊑D B⊑D → B⊑D)
consistency→lub ℕ~★ =
  ℕ , mkLub ⊑-ℕ ⊑-★ (λ A⊑D B⊑D → A⊑D)
consistency→lub {B = A ⇒ B} (★~⇒ A~★ ★~B) =
  (A ⇒ B) ,
  mkLub ⊑-★ (⊑-⇒ ⊑-refl ⊑-refl) (λ A⊑D B⊑D → B⊑D)
consistency→lub {A = A ⇒ B} (⇒~★ ★~A B~★) =
  (A ⇒ B) ,
  mkLub (⊑-⇒ ⊑-refl ⊑-refl) ⊑-★ (λ A⊑D B⊑D → A⊑D)
consistency→lub {A = A₁ ⇒ B₁} {B = C₁ ⇒ D₁} (~-⇒ C~A B~D)
  with consistency→lub C~A
     | consistency→lub B~D
... | Jdom , (C⊑Jdom , (A⊑Jdom , leastDom))
    | Jcod , (B⊑Jcod , (D⊑Jcod , leastCod)) =
  (Jdom ⇒ Jcod) ,
  mkLub (⊑-⇒ A⊑Jdom B⊑Jcod) (⊑-⇒ C⊑Jdom D⊑Jcod) least
  where
    least :
      ∀ {X} →
      (A₁ ⇒ B₁) ⊑ X →
      (C₁ ⇒ D₁) ⊑ X →
      (Jdom ⇒ Jcod) ⊑ X
    least (⊑-⇒ A⊑X B⊑X) (⊑-⇒ C⊑X D⊑X) =
      ⊑-⇒ (leastDom C⊑X A⊑X) (leastCod B⊑X D⊑X)

lub→consistency : ∀ {A B} → Σ Ty (Lub A B) → A ~ B
lub→consistency (_ , (A⊑C , (B⊑C , least))) =
  upper-bounds-consistent A⊑C B⊑C

consistency-iff-lub :
  ∀ {A B} →
  (A ~ B → Σ Ty (Lub A B)) ×
  (Σ Ty (Lub A B) → A ~ B)
consistency-iff-lub = consistency→lub , lub→consistency

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

ground-⊑-equal : ∀ {G H}
  → Ground G
  → Ground H
  → G ⊑ H
  → G ≡ H
ground-⊑-equal g h G⊑H = ground-upper-unique g h G⊑H ⊑-refl

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
