module Consistency where

-- File Charter:
--   * Type consistency.

open import Types
open import Imprecision

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data CMode : Set where
  left right both : CMode

CCtx : Set
CCtx = List CMode

boths : ℕ → CCtx → CCtx
boths zero Γ = Γ
boths (suc n) Γ = both ∷ boths n Γ

leftMode : CMode → VarMode
leftMode left = plain
leftMode right = ν-bound
leftMode both = plain

rightMode : CMode → VarMode
rightMode left = ν-bound
rightMode right = plain
rightMode both = plain

leftICtx : CCtx → ICtx
leftICtx [] = []
leftICtx (m ∷ Γ) = leftMode m ∷ leftICtx Γ

rightICtx : CCtx → ICtx
rightICtx [] = []
rightICtx (m ∷ Γ) = rightMode m ∷ rightICtx Γ

length-leftICtx : ∀ Γ → length (leftICtx Γ) ≡ length Γ
length-leftICtx [] = refl
length-leftICtx (m ∷ Γ) = cong suc (length-leftICtx Γ)

length-rightICtx : ∀ Γ → length (rightICtx Γ) ≡ length Γ
length-rightICtx [] = refl
length-rightICtx (m ∷ Γ) = cong suc (length-rightICtx Γ)

leftICtx-boths[] : ∀ Δ → leftICtx (boths Δ []) ≡ plains Δ []
leftICtx-boths[] zero = refl
leftICtx-boths[] (suc Δ) = cong (plain ∷_) (leftICtx-boths[] Δ)

rightICtx-boths[] : ∀ Δ → rightICtx (boths Δ []) ≡ plains Δ []
rightICtx-boths[] zero = refl
rightICtx-boths[] (suc Δ) = cong (plain ∷_) (rightICtx-boths[] Δ)

infix 4 _∋ᶜ_∶_
data _∋ᶜ_∶_ : CCtx → TyVar → CMode → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ᶜ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ᶜ X ∶ m → (m′ ∷ Γ) ∋ᶜ suc X ∶ m

left-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  leftICtx Γ ∋ X ∶ plain
left-lookup-left here = here
left-lookup-left (there x∈) = there (left-lookup-left x∈)

right-lookup-left :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ left →
  rightICtx Γ ∋ X ∶ ν-bound
right-lookup-left here = here
right-lookup-left (there x∈) = there (right-lookup-left x∈)

left-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  leftICtx Γ ∋ X ∶ ν-bound
left-lookup-right here = here
left-lookup-right (there x∈) = there (left-lookup-right x∈)

right-lookup-right :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ right →
  rightICtx Γ ∋ X ∶ plain
right-lookup-right here = here
right-lookup-right (there x∈) = there (right-lookup-right x∈)

left-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  leftICtx Γ ∋ X ∶ plain
left-lookup-both here = here
left-lookup-both (there x∈) = there (left-lookup-both x∈)

right-lookup-both :
  ∀ {Γ X} →
  Γ ∋ᶜ X ∶ both →
  rightICtx Γ ∋ X ∶ plain
right-lookup-both here = here
right-lookup-both (there x∈) = there (right-lookup-both x∈)

infix 4 _⊢_~_

data _⊢_~_ (Γ : CCtx) : Ty → Ty → Set where

  ★-~-★ : Γ ⊢ ★ ~ ★

  X-~-X : ∀ {X} →
    Γ ∋ᶜ X ∶ both →
    Γ ⊢ ＇ X ~ ＇ X

  ι-~-ι : ∀ {ι} →
    Γ ⊢ ‵ ι ~ ‵ ι

  ⇒-~-⇒ : ∀ {A A′ B B′} →
    Γ ⊢ A ~ A′ →
    Γ ⊢ B ~ B′ →
    Γ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

  ∀-~-∀ : ∀ {A B} →
    both ∷ Γ ⊢ A ~ B →
    Γ ⊢ (`∀ A) ~ (`∀ B)

  A-~-★ : ∀ {A G} →
    Ground G →
    Γ ⊢ A ~ G →
    Γ ⊢ A ~ ★

  ★-~-B : ∀ {B H} →
    Ground H →
    Γ ⊢ H ~ B →
    Γ ⊢ ★ ~ B

  νX-~-★ : ∀ {X} →
    Γ ∋ᶜ X ∶ left →
    Γ ⊢ ＇ X ~ ★

  ★-~-νX : ∀ {X} →
    Γ ∋ᶜ X ∶ right →
    Γ ⊢ ★ ~ ＇ X

  ∀-~-B : ∀ {A B} →
    WfTy (length Γ) 0 B →
    left ∷ Γ ⊢ A ~ ⇑ᵗ B →
    Γ ⊢ (`∀ A) ~ B

  A-~-∀ : ∀ {A B} →
    WfTy (length Γ) 0 A →
    right ∷ Γ ⊢ ⇑ᵗ A ~ B →
    Γ ⊢ A ~ (`∀ B)

coerce :
  ∀ {Γ A C} →
  Γ ⊢ A ~ C →
  Imp × Imp
coerce ★-~-★ =
  ★⊑★ , ★⊑★
coerce (X-~-X {X} x∈) =
  X⊑X X , X⊑X X
coerce (ι-~-ι {ι}) =
  ι⊑ι ι , ι⊑ι ι
coerce (⇒-~-⇒ A~A′ B~B′) with coerce A~A′ | coerce B~B′
coerce (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑ =
  A⇒B⊑A′⇒B′ pA⊒ pB⊒ ,
  A⇒B⊑A′⇒B′ pA⊑ pB⊑
coerce (∀-~-∀ A~B) with coerce A~B
coerce (∀-~-∀ A~B) | p⊒ , p⊑ =
  `∀A⊑∀B p⊒ , `∀A⊑∀B p⊑
coerce (A-~-★ g A~G) with coerce A~G
coerce (A-~-★ g A~G) | p⊒ , p⊑ =
  p⊒ , A⊑★ p⊑
coerce (★-~-B h H~B) with coerce H~B
coerce (★-~-B h H~B) | p⊒ , p⊑ =
  A⊑★ p⊒ , p⊑
coerce (νX-~-★ {X} x∈) =
  X⊑X X , X⊑★ X
coerce (★-~-νX {X} x∈) =
  X⊑★ X , X⊑X X
coerce (∀-~-B {B = B} wfB A~⇑B) with coerce A~⇑B
coerce (∀-~-B {B = B} wfB A~⇑B) | p⊒ , p⊑ =
  `∀A⊑∀B p⊒ , `∀A⊑B B p⊑
coerce (A-~-∀ {A = A} wfA ⇑A~B) with coerce ⇑A~B
coerce (A-~-∀ {A = A} wfA ⇑A~B) | p⊒ , p⊑ =
  `∀A⊑B A p⊒ , `∀A⊑∀B p⊑
