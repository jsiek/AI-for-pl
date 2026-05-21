module Consistency where

-- File Charter:
--   * Type consistency.

open import Types
open import Imprecision

open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Consistency context and lookup
------------------------------------------------------------------------

data CMode : Set where
  X~★ ★~X X~X neither : CMode

CCtx : Set
CCtx = List CMode

infix 4 _∋ᶜ_∶_
data _∋ᶜ_∶_ : CCtx → TyVar → CMode → Set where
  here : ∀ {Γ m} → (m ∷ Γ) ∋ᶜ zero ∶ m
  there : ∀ {Γ X m m′} → Γ ∋ᶜ X ∶ m → (m′ ∷ Γ) ∋ᶜ suc X ∶ m

extend-X~X : ℕ → CCtx → CCtx
extend-X~X n Γ = (replicate n X~X) ++ Γ

leftMode : CMode → VarPrec
leftMode X~★ = X⊑X
leftMode ★~X = X⊑★
leftMode X~X = X⊑X
leftMode neither = X⊑★

rightMode : CMode → VarPrec
rightMode X~★ = X⊑★
rightMode ★~X = X⊑X
rightMode X~X = X⊑X
rightMode neither = X⊑★

leftICtx : CCtx → VarPrecCtx
leftICtx [] = []
leftICtx (m ∷ Γ) = leftMode m ∷ leftICtx Γ

rightICtx : CCtx → VarPrecCtx
rightICtx [] = []
rightICtx (m ∷ Γ) = rightMode m ∷ rightICtx Γ

------------------------------------------------------------------------
-- Type Consistency
------------------------------------------------------------------------

infix 4 _⊢_~_

data _⊢_~_ (Γ : CCtx) : Ty → Ty → Set where

  ★-~-★ : Γ ⊢ ★ ~ ★

  X-~-X : ∀ {X} →
    Γ ∋ᶜ X ∶ X~X →
    Γ ⊢ ＇ X ~ ＇ X

  ι-~-ι : ∀ {ι} →
    Γ ⊢ ‵ ι ~ ‵ ι

  ⇒-~-⇒ : ∀ {A A′ B B′} →
    Γ ⊢ A ~ A′ →
    Γ ⊢ B ~ B′ →
    Γ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

  ∀-~-∀ : ∀ {A B} →
    X~X ∷ Γ ⊢ A ~ B →
    Γ ⊢ (`∀ A) ~ (`∀ B)

  A-~-★ : ∀ {A G} →
    Non★ A →
    Non∀ A →
    Ground G →
    Γ ⊢ A ~ G →
    Γ ⊢ A ~ ★

  ★-~-B : ∀ {B H} →
    Non★ B →
    Non∀ B →
    Ground H →
    Γ ⊢ H ~ B →
    Γ ⊢ ★ ~ B

  νX-~-★ : ∀ {X} →
    Γ ∋ᶜ X ∶ X~★ →
    Γ ⊢ ＇ X ~ ★

  ★-~-νX : ∀ {X} →
    Γ ∋ᶜ X ∶ ★~X →
    Γ ⊢ ★ ~ ＇ X

  ∀-~-B : ∀ {A B} →
    WfTy (length Γ) 0 B →
    X~★ ∷ Γ ⊢ A ~ ⇑ᵗ B →
    Γ ⊢ (`∀ A) ~ B

  A-~-∀ : ∀ {A B} →
    WfTy (length Γ) 0 A →
    ★~X ∷ Γ ⊢ ⇑ᵗ A ~ B →
    Γ ⊢ A ~ (`∀ B)

------------------------------------------------------------------------
-- Generate a pair of imprecisions from consistent types
------------------------------------------------------------------------

coerce :
  ∀ {Γ A C} →
  Γ ⊢ A ~ C →
  Imp × Imp
coerce ★-~-★ =
  id★ , id★
coerce (X-~-X {X} x∈) =
  idₓ X , idₓ X
coerce (ι-~-ι {ι}) =
  idι ι , idι ι
coerce (⇒-~-⇒ A~A′ B~B′) with coerce A~A′ | coerce B~B′
coerce (⇒-~-⇒ A~A′ B~B′)
    | pA⊒ , pA⊑
    | pB⊒ , pB⊑ =
  pA⊒ ↦ pB⊒ ,
  pA⊑ ↦ pB⊑
coerce (∀-~-∀ A~B) with coerce A~B
coerce (∀-~-∀ A~B) | p⊒ , p⊑ =
  ‵∀ p⊒ , ‵∀ p⊑
coerce (A-~-★ n★ n∀ g A~G) with coerce A~G
coerce (A-~-★ n★ n∀ g A~G) | p⊒ , p⊑ =
  p⊒ , p⊑ !
coerce (★-~-B n★ n∀ h H~B) with coerce H~B
coerce (★-~-B n★ n∀ h H~B) | p⊒ , p⊑ =
  p⊒ ! , p⊑
coerce (νX-~-★ {X} x∈) =
  idₓ X , ‵ X !
coerce (★-~-νX {X} x∈) =
  ‵ X ! , idₓ X
coerce (∀-~-B {B = B} wfB A~⇑B) with coerce A~⇑B
coerce (∀-~-B {B = B} wfB A~⇑B) | p⊒ , p⊑ =
  ‵∀ p⊒ , ν p⊑
coerce (A-~-∀ {A = A} wfA ⇑A~B) with coerce ⇑A~B
coerce (A-~-∀ {A = A} wfA ⇑A~B) | p⊒ , p⊑ =
  ν p⊒ , ‵∀ p⊑


coerce-⊒ : ∀ {Γ A C} → Γ ⊢ A ~ C → Imp
coerce-⊒ A~C = proj₁ (coerce A~C)

coerce-⊑ : ∀ {Γ A C} → Γ ⊢ A ~ C → Imp
coerce-⊑ A~C = proj₂ (coerce A~C)
