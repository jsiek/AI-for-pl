
module ConsistencyAlt where

-- File Charter:
--   * Type consistency.

open import Types
open import Imprecision

open import Data.Bool using (Bool; true; false)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; Dec)

------------------------------------------------------------------------
-- Consistency context and lookup
------------------------------------------------------------------------

-- Assumptions
data Assm : Set where
  _~ᶜ★ : TyVar → Assm
  ★~ᶜ_ : TyVar → Assm
  _~ᶜ_ : TyVar → TyVar → Assm

CCtx : Set
CCtx = List Assm

⇑ₐ : Assm → Assm
⇑ₐ (X ~ᶜ★) = suc X ~ᶜ★
⇑ₐ (★~ᶜ Y) = ★~ᶜ Y
⇑ₐ (X ~ᶜ Y) = suc X ~ᶜ suc Y

⇑ᴸₐ : Assm → Assm
⇑ᴸₐ (X ~ᶜ★) = suc X ~ᶜ★
⇑ᴸₐ (★~ᶜ Y) = ★~ᶜ Y
⇑ᴸₐ (X ~ᶜ Y) = suc X ~ᶜ Y

⇑ᴿₐ : Assm → Assm
⇑ᴿₐ (X ~ᶜ★) = X ~ᶜ★
⇑ᴿₐ (★~ᶜ Y) = ★~ᶜ suc Y
⇑ᴿₐ (X ~ᶜ Y) = X ~ᶜ suc Y

⇑ : List Assm → List Assm
⇑ = λ Γ → map ⇑ₐ Γ
⇑ᴸ = λ Γ → map ⇑ᴸₐ Γ
⇑ᴿ = λ Γ → map ⇑ᴿₐ Γ

------------------------------------------------------------------------
-- Type Consistency
------------------------------------------------------------------------

infix 4 _⊢_~_

data _⊢_~_ (Γ : CCtx) : Ty → Ty → Set where

  ★-~-★ : Γ ⊢ ★ ~ ★

  X-~-Y : ∀ {X Y}
    → (X ~ᶜ Y) ∈ Γ
    ---------------
    → Γ ⊢ ＇ X ~ ＇ Y

  ι-~-ι : ∀ {ι} →
    Γ ⊢ ‵ ι ~ ‵ ι

  ⇒-~-⇒ : ∀ {A A′ B B′} →
    Γ ⊢ A ~ A′ →
    Γ ⊢ B ~ B′ →
    -----------------------
    Γ ⊢ (A ⇒ B) ~ (A′ ⇒ B′)

  ∀-~-∀ : ∀ {A B} 
    → (0 ~ᶜ 0) ∷ (⇑ Γ) ⊢ A ~ B
    ------------------------
    → Γ ⊢ (`∀ A) ~ (`∀ B)

  ι-~-★ : ∀ {ι}
    → Γ ⊢ ‵ ι ~ ★

  ⇒-~-★ : ∀ {A₁ A₂}
    → Γ ⊢ A₁ ~ ★
    → Γ ⊢ A₂ ~ ★
    -----------------
    → Γ ⊢ A₁ ⇒ A₂ ~ ★

  νX-~-★ : ∀ {X}
    → (X ~ᶜ★) ∈ Γ
    ---------------
    → Γ ⊢ ＇ X ~ ★

  ★-~-ι : ∀ {ι} →
    Γ ⊢ ★ ~ ‵ ι
    
  ★-~-⇒ : ∀ {B₁ B₂} →
    Γ ⊢ ★ ~ B₁ →
    Γ ⊢ ★ ~ B₂ →
    ---------------
    Γ ⊢ ★ ~ B₁ ⇒ B₂

  ★-~-νX : ∀ {X}
    → (★~ᶜ X) ∈ Γ
    ---------------
    → Γ ⊢ ★ ~ ＇ X

  ∀-~-B : ∀ {A B}
    → occurs zero A ≡ true
    → (0 ~ᶜ★) ∷ ⇑ᴸ Γ ⊢ A ~ B
    ------------------------
    → Γ ⊢ (`∀ A) ~ B

  A-~-∀ : ∀ {A B}
    → occurs zero B ≡ true
    → (★~ᶜ 0) ∷ ⇑ᴿ Γ ⊢ A ~ B
    ------------------------
    → Γ ⊢ A ~ (`∀ B)

------------------------------------------------------------------------
-- Decide Consistency
------------------------------------------------------------------------

split-∀ : Ty → ℕ × (∃[ A ] Non∀ A)
split-∀ (＇ X) = 0 , ＇ X , non∀-＇
split-∀ (｀ α) = 0 , (｀ α) , non∀-｀
split-∀ (‵ ι) = 0 , ‵ ι , non∀-‵
split-∀ ★ = 0 , ★ , non∀-★
split-∀ (A ⇒ B) = 0 , A ⇒ B , non∀-⇒
split-∀ (`∀ A)
    with split-∀ A
... | n , B , n∀ = suc n , B , n∀

-- _~ₐ_ : Assm → Assm → 

clash : Assm → Assm → Bool
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) with X ≟ X′ | Y ≟ Y′
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | yes _ = false
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | no _ = true
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | yes _ = true
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | no _ = false
clash _ _ = false

consistent-assm? : Assm → CCtx → Bool
consistent-assm? a [] = true
consistent-assm? a (b ∷ Γ) with clash a b
consistent-assm? a (b ∷ Γ) | true = false
consistent-assm? a (b ∷ Γ) | false = consistent-assm? a Γ

consistent-ctx? : CCtx → CCtx → Bool
consistent-ctx? [] Γ₂ = true
consistent-ctx? (a ∷ Γ₁) Γ₂ with consistent-assm? a Γ₂
consistent-ctx? (a ∷ Γ₁) Γ₂ | true = consistent-ctx? Γ₁ Γ₂
consistent-ctx? (a ∷ Γ₁) Γ₂ | false = false

∈-++ˡ : ∀ {A : Set} {x : A} {xs ys : List A} → x ∈ xs → x ∈ xs ++ ys
∈-++ˡ (here refl) = here refl
∈-++ˡ (there x∈) = there (∈-++ˡ x∈)

∈-++ʳ : ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
  x ∈ ys → x ∈ xs ++ ys
∈-++ʳ [] x∈ = x∈
∈-++ʳ (_ ∷ xs) x∈ = there (∈-++ʳ xs x∈)

append-[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
append-[] [] = refl
append-[] (x ∷ xs) = cong (λ ys → x ∷ ys) (append-[] xs)

⇑-++ : ∀ Γ₁ Γ₂ → ⇑ (Γ₁ ++ Γ₂) ≡ ⇑ Γ₁ ++ ⇑ Γ₂
⇑-++ [] Γ₂ = refl
⇑-++ (a ∷ Γ₁) Γ₂ = cong (λ xs → ⇑ₐ a ∷ xs) (⇑-++ Γ₁ Γ₂)

⇑ᴸ-++ : ∀ Γ₁ Γ₂ → ⇑ᴸ (Γ₁ ++ Γ₂) ≡ ⇑ᴸ Γ₁ ++ ⇑ᴸ Γ₂
⇑ᴸ-++ [] Γ₂ = refl
⇑ᴸ-++ (a ∷ Γ₁) Γ₂ = cong (λ xs → ⇑ᴸₐ a ∷ xs) (⇑ᴸ-++ Γ₁ Γ₂)

⇑ᴿ-++ : ∀ Γ₁ Γ₂ → ⇑ᴿ (Γ₁ ++ Γ₂) ≡ ⇑ᴿ Γ₁ ++ ⇑ᴿ Γ₂
⇑ᴿ-++ [] Γ₂ = refl
⇑ᴿ-++ (a ∷ Γ₁) Γ₂ = cong (λ xs → ⇑ᴿₐ a ∷ xs) (⇑ᴿ-++ Γ₁ Γ₂)

cast-ctx : ∀ {Γ Γ′ A B} → Γ ≡ Γ′ → Γ ⊢ A ~ B → Γ′ ⊢ A ~ B
cast-ctx refl A~B = A~B

cast-left : ∀ {Γ A A′ B} → A ≡ A′ → Γ ⊢ A ~ B → Γ ⊢ A′ ~ B
cast-left refl A~B = A~B

cast-right : ∀ {Γ A B B′} → B ≡ B′ → Γ ⊢ A ~ B → Γ ⊢ A ~ B′
cast-right refl A~B = A~B

∈-++-mid : ∀ {A : Set} {x : A} (Δ Γ₁ : List A) {Γ₂ : List A} →
  x ∈ (Δ ++ Γ₂) → x ∈ (Δ ++ Γ₁ ++ Γ₂)
∈-++-mid [] Γ₁ x∈ = ∈-++ʳ Γ₁ x∈
∈-++-mid (_ ∷ Δ) Γ₁ (here refl) = here refl
∈-++-mid (_ ∷ Δ) Γ₁ (there x∈) = there (∈-++-mid Δ Γ₁ x∈)

ctx-∀-split : ∀ Δ Γ₂ →
  (0 ~ᶜ 0) ∷ ⇑ (Δ ++ Γ₂) ≡ ((0 ~ᶜ 0) ∷ ⇑ Δ) ++ ⇑ Γ₂
ctx-∀-split Δ Γ₂ = cong (λ xs → (0 ~ᶜ 0) ∷ xs) (⇑-++ Δ Γ₂)

ctx-∀ᴸ-split : ∀ Δ Γ₂ →
  (0 ~ᶜ★) ∷ ⇑ᴸ (Δ ++ Γ₂) ≡ ((0 ~ᶜ★) ∷ ⇑ᴸ Δ) ++ ⇑ᴸ Γ₂
ctx-∀ᴸ-split Δ Γ₂ = cong (λ xs → (0 ~ᶜ★) ∷ xs) (⇑ᴸ-++ Δ Γ₂)

ctx-∀ᴿ-split : ∀ Δ Γ₂ →
  (★~ᶜ 0) ∷ ⇑ᴿ (Δ ++ Γ₂) ≡ ((★~ᶜ 0) ∷ ⇑ᴿ Δ) ++ ⇑ᴿ Γ₂
ctx-∀ᴿ-split Δ Γ₂ = cong (λ xs → (★~ᶜ 0) ∷ xs) (⇑ᴿ-++ Δ Γ₂)

⇑-++-nest : ∀ Δ Γ₁ Γ₂ →
  ⇑ Δ ++ (⇑ Γ₁ ++ ⇑ Γ₂) ≡ ⇑ (Δ ++ (Γ₁ ++ Γ₂))
⇑-++-nest Δ Γ₁ Γ₂ =
  trans (cong (λ xs → ⇑ Δ ++ xs) (sym (⇑-++ Γ₁ Γ₂)))
        (sym (⇑-++ Δ (Γ₁ ++ Γ₂)))

⇑ᴸ-++-nest : ∀ Δ Γ₁ Γ₂ →
  ⇑ᴸ Δ ++ (⇑ᴸ Γ₁ ++ ⇑ᴸ Γ₂) ≡ ⇑ᴸ (Δ ++ (Γ₁ ++ Γ₂))
⇑ᴸ-++-nest Δ Γ₁ Γ₂ =
  trans (cong (λ xs → ⇑ᴸ Δ ++ xs) (sym (⇑ᴸ-++ Γ₁ Γ₂)))
        (sym (⇑ᴸ-++ Δ (Γ₁ ++ Γ₂)))

⇑ᴿ-++-nest : ∀ Δ Γ₁ Γ₂ →
  ⇑ᴿ Δ ++ (⇑ᴿ Γ₁ ++ ⇑ᴿ Γ₂) ≡ ⇑ᴿ (Δ ++ (Γ₁ ++ Γ₂))
⇑ᴿ-++-nest Δ Γ₁ Γ₂ =
  trans (cong (λ xs → ⇑ᴿ Δ ++ xs) (sym (⇑ᴿ-++ Γ₁ Γ₂)))
        (sym (⇑ᴿ-++ Δ (Γ₁ ++ Γ₂)))

ctx-∀-join : ∀ Δ Γ₁ Γ₂ →
  ((0 ~ᶜ 0) ∷ ⇑ Δ) ++ (⇑ Γ₁ ++ ⇑ Γ₂) ≡
  (0 ~ᶜ 0) ∷ ⇑ (Δ ++ (Γ₁ ++ Γ₂))
ctx-∀-join Δ Γ₁ Γ₂ =
  cong (λ xs → (0 ~ᶜ 0) ∷ xs) (⇑-++-nest Δ Γ₁ Γ₂)

ctx-∀ᴸ-join : ∀ Δ Γ₁ Γ₂ →
  ((0 ~ᶜ★) ∷ ⇑ᴸ Δ) ++ (⇑ᴸ Γ₁ ++ ⇑ᴸ Γ₂) ≡
  (0 ~ᶜ★) ∷ ⇑ᴸ (Δ ++ (Γ₁ ++ Γ₂))
ctx-∀ᴸ-join Δ Γ₁ Γ₂ =
  cong (λ xs → (0 ~ᶜ★) ∷ xs) (⇑ᴸ-++-nest Δ Γ₁ Γ₂)

ctx-∀ᴿ-join : ∀ Δ Γ₁ Γ₂ →
  ((★~ᶜ 0) ∷ ⇑ᴿ Δ) ++ (⇑ᴿ Γ₁ ++ ⇑ᴿ Γ₂) ≡
  (★~ᶜ 0) ∷ ⇑ᴿ (Δ ++ (Γ₁ ++ Γ₂))
ctx-∀ᴿ-join Δ Γ₁ Γ₂ =
  cong (λ xs → (★~ᶜ 0) ∷ xs) (⇑ᴿ-++-nest Δ Γ₁ Γ₂)

wk-mid : ∀ (Δ Γ₁ : CCtx) {Γ₂ A B} →
  (Δ ++ Γ₂) ⊢ A ~ B →
  (Δ ++ Γ₁ ++ Γ₂) ⊢ A ~ B
wk-mid Δ Γ₁ ★-~-★ = ★-~-★
wk-mid Δ Γ₁ (X-~-Y x∈) = X-~-Y (∈-++-mid Δ Γ₁ x∈)
wk-mid Δ Γ₁ ι-~-ι = ι-~-ι
wk-mid Δ Γ₁ (⇒-~-⇒ A~A′ B~B′) = ⇒-~-⇒ (wk-mid Δ Γ₁ A~A′) (wk-mid Δ Γ₁ B~B′)
wk-mid Δ Γ₁ (∀-~-∀ A~B) =
  ∀-~-∀
    (cast-ctx (ctx-∀-join Δ Γ₁ _)
      (wk-mid ((0 ~ᶜ 0) ∷ ⇑ Δ) (⇑ Γ₁)
        (cast-ctx (ctx-∀-split Δ _) A~B)))
wk-mid Δ Γ₁ ι-~-★ = ι-~-★
wk-mid Δ Γ₁ (⇒-~-★ A₁~★ A₂~★) = ⇒-~-★ (wk-mid Δ Γ₁ A₁~★) (wk-mid Δ Γ₁ A₂~★)
wk-mid Δ Γ₁ (νX-~-★ x∈) = νX-~-★ (∈-++-mid Δ Γ₁ x∈)
wk-mid Δ Γ₁ ★-~-ι = ★-~-ι
wk-mid Δ Γ₁ (★-~-⇒ ★~B₁ ★~B₂) = ★-~-⇒ (wk-mid Δ Γ₁ ★~B₁) (wk-mid Δ Γ₁ ★~B₂)
wk-mid Δ Γ₁ (★-~-νX x∈) = ★-~-νX (∈-++-mid Δ Γ₁ x∈)
wk-mid Δ Γ₁ (∀-~-B occA A~B) =
  ∀-~-B occA
    (cast-ctx (ctx-∀ᴸ-join Δ Γ₁ _)
      (wk-mid ((0 ~ᶜ★) ∷ ⇑ᴸ Δ) (⇑ᴸ Γ₁)
        (cast-ctx (ctx-∀ᴸ-split Δ _) A~B)))
wk-mid Δ Γ₁ (A-~-∀ occB A~B) =
  A-~-∀ occB
    (cast-ctx (ctx-∀ᴿ-join Δ Γ₁ _)
      (wk-mid ((★~ᶜ 0) ∷ ⇑ᴿ Δ) (⇑ᴿ Γ₁)
        (cast-ctx (ctx-∀ᴿ-split Δ _) A~B)))

wk-++ˡ : ∀ {Γ₁ Γ₂ A B} → Γ₁ ⊢ A ~ B → Γ₁ ++ Γ₂ ⊢ A ~ B
wk-++ˡ {Γ₁} {Γ₂} {A} {B} A~B =
  cast-ctx (cong (λ ys → Γ₁ ++ ys) (append-[] Γ₂))
           (wk-mid Γ₁ Γ₂ (cast-ctx (sym (append-[] Γ₁)) A~B))

wk-++ʳ : ∀ (Γ₁ : CCtx) {Γ₂ A B} → Γ₂ ⊢ A ~ B → Γ₁ ++ Γ₂ ⊢ A ~ B
wk-++ʳ Γ₁ A~B = wk-mid [] Γ₁ A~B

{-# TERMINATING #-}
consistent? : (A B : Ty) → Maybe (Σ[ Γ ∈ CCtx ] Γ ⊢ A ~ B)

add∀ : ℕ → Ty → Ty
add∀ zero A = A
add∀ (suc n) A = `∀ (add∀ n A)

add∀-step : ∀ n A → add∀ n (`∀ A) ≡ add∀ (suc n) A
add∀-step zero A = refl
add∀-step (suc n) A = cong `∀ (add∀-step n A)

split-n : ℕ × (∃[ A ] Non∀ A) → ℕ
split-n = proj₁

split-body : ℕ × (∃[ A ] Non∀ A) → Ty
split-body p = proj₁ (proj₂ p)

split-add∀ : ∀ A → add∀ (split-n (split-∀ A)) (split-body (split-∀ A)) ≡ A
split-add∀ (＇ X) = refl
split-add∀ (｀ α) = refl
split-add∀ (‵ ι) = refl
split-add∀ ★ = refl
split-add∀ (A ⇒ B) = refl
split-add∀ (`∀ A) with split-∀ A | split-add∀ A
... | n , A′ , n∀A | eq = cong `∀ eq

split-add∀-from :
  ∀ {A p} →
  split-∀ A ≡ p →
  add∀ (split-n p) (split-body p) ≡ A
split-add∀-from {A} {p} eq =
  subst (λ q → add∀ (split-n q) (split-body q) ≡ A) eq (split-add∀ A)

unshiftₐ : (a : Assm) → Maybe (Σ[ b ∈ Assm ] ⇑ₐ b ≡ a)
unshiftₐ (suc X ~ᶜ★) = just (X ~ᶜ★ , refl)
unshiftₐ (★~ᶜ Y) = just (★~ᶜ Y , refl)
unshiftₐ (suc X ~ᶜ suc Y) = just (X ~ᶜ Y , refl)
unshiftₐ _ = nothing

unshiftᴸₐ : (a : Assm) → Maybe (Σ[ b ∈ Assm ] ⇑ᴸₐ b ≡ a)
unshiftᴸₐ (suc X ~ᶜ★) = just (X ~ᶜ★ , refl)
unshiftᴸₐ (★~ᶜ Y) = just (★~ᶜ Y , refl)
unshiftᴸₐ (suc X ~ᶜ Y) = just (X ~ᶜ Y , refl)
unshiftᴸₐ _ = nothing

unshiftᴿₐ : (a : Assm) → Maybe (Σ[ b ∈ Assm ] ⇑ᴿₐ b ≡ a)
unshiftᴿₐ (X ~ᶜ★) = just (X ~ᶜ★ , refl)
unshiftᴿₐ (★~ᶜ suc Y) = just (★~ᶜ Y , refl)
unshiftᴿₐ (X ~ᶜ suc Y) = just (X ~ᶜ Y , refl)
unshiftᴿₐ _ = nothing

unshift : (Γ : CCtx) → Maybe (Σ[ Δ ∈ CCtx ] ⇑ Δ ≡ Γ)
unshift [] = just ([] , refl)
unshift (a ∷ Γ)
    with unshiftₐ a | unshift Γ
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (b , eq₁) | just (Δ , eq₂) =
      just (b ∷ Δ , trans (cong (λ xs → ⇑ₐ b ∷ xs) eq₂)
                           (cong (λ x → x ∷ Γ) eq₁))

unshiftᴸ : (Γ : CCtx) → Maybe (Σ[ Δ ∈ CCtx ] ⇑ᴸ Δ ≡ Γ)
unshiftᴸ [] = just ([] , refl)
unshiftᴸ (a ∷ Γ)
    with unshiftᴸₐ a | unshiftᴸ Γ
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (b , eq₁) | just (Δ , eq₂) =
      just (b ∷ Δ , trans (cong (λ xs → ⇑ᴸₐ b ∷ xs) eq₂)
                           (cong (λ x → x ∷ Γ) eq₁))

unshiftᴿ : (Γ : CCtx) → Maybe (Σ[ Δ ∈ CCtx ] ⇑ᴿ Δ ≡ Γ)
unshiftᴿ [] = just ([] , refl)
unshiftᴿ (a ∷ Γ)
    with unshiftᴿₐ a | unshiftᴿ Γ
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (b , eq₁) | just (Δ , eq₂) =
      just (b ∷ Δ , trans (cong (λ xs → ⇑ᴿₐ b ∷ xs) eq₂)
                           (cong (λ x → x ∷ Γ) eq₁))

lift-∀ :
  ∀ (n m : ℕ) {A B Γ} →
  Γ ⊢ A ~ B →
  Maybe (Σ[ Δ ∈ CCtx ] Δ ⊢ add∀ n A ~ add∀ m B)
lift-∀ zero zero {Γ = Γ} A~B = just (Γ , A~B)
lift-∀ n m {A} {B} {Γ} A~B with Γ
... | [] = nothing
... | (0 ~ᶜ 0) ∷ Γ′ with unshift Γ′
...   | nothing = nothing
...   | just (Δ , eq) = step-both n m eq A~B
  where
  step-both :
    ∀ (n m : ℕ) {A B Γ Γ′} →
    ⇑ Γ′ ≡ Γ →
    ((0 ~ᶜ 0) ∷ Γ) ⊢ A ~ B →
    Maybe (Σ[ Δ ∈ CCtx ] Δ ⊢ add∀ n A ~ add∀ m B)
  step-both zero _ eq h = nothing
  step-both _ zero eq h = nothing
  step-both (suc n′) (suc m′) {A} {B} {Γ} {Γ′} eq h
      with lift-∀ n′ m′ (∀-~-∀ (cast-ctx (cong (λ xs → (0 ~ᶜ 0) ∷ xs) (sym eq)) h))
  ... | nothing = nothing
  ... | just (Ξ , k) =
        just (Ξ , cast-right (add∀-step m′ B) (cast-left (add∀-step n′ A) k))
lift-∀ n m {A} {B} {Γ} A~B | (0 ~ᶜ★) ∷ Γ′ with occurs zero A | unshiftᴸ Γ′
... | false | _ = nothing
... | true | nothing = nothing
... | true | just (Δ , eq) = step-left n m eq A~B
  where
  step-left :
    ∀ (n m : ℕ) {A B Γ Γ′} →
    ⇑ᴸ Γ′ ≡ Γ →
    ((0 ~ᶜ★) ∷ Γ) ⊢ A ~ B →
    Maybe (Σ[ Δ ∈ CCtx ] Δ ⊢ add∀ n A ~ add∀ m B)
  step-left zero m eq h = nothing
  step-left (suc n′) m {A} {B} {Γ} {Γ′} eq h with occurs zero A in occA
  ... | false = nothing
  ... | true
      with lift-∀ n′ m (∀-~-B occA (cast-ctx (cong (λ xs → (0 ~ᶜ★) ∷ xs) (sym eq)) h))
  ...   | nothing = nothing
  ...   | just (Ξ , k) = just (Ξ , cast-left (add∀-step n′ A) k)
lift-∀ n m {A} {B} {Γ} A~B | (★~ᶜ 0) ∷ Γ′ with occurs zero B | unshiftᴿ Γ′
... | false | _ = nothing
... | true | nothing = nothing
... | true | just (Δ , eq) = step-right n m eq A~B
  where
  step-right :
    ∀ (n m : ℕ) {A B Γ Γ′} →
    ⇑ᴿ Γ′ ≡ Γ →
    ((★~ᶜ 0) ∷ Γ) ⊢ A ~ B →
    Maybe (Σ[ Δ ∈ CCtx ] Δ ⊢ add∀ n A ~ add∀ m B)
  step-right n zero eq h = nothing
  step-right n (suc m′) {A} {B} {Γ} {Γ′} eq h with occurs zero B in occB
  ... | false = nothing
  ... | true
      with lift-∀ n m′ (A-~-∀ occB (cast-ctx (cong (λ xs → (★~ᶜ 0) ∷ xs) (sym eq)) h))
  ...   | nothing = nothing
  ...   | just (Ξ , k) = just (Ξ , cast-right (add∀-step m′ B) k)
lift-∀ n m {A} {B} {Γ} A~B | _ = nothing

core-consistent? : (A B : Ty) → Non∀ A → Non∀ B → Maybe (Σ[ Γ ∈ CCtx ] Γ ⊢ A ~ B)
core-consistent? (＇ X) (＇ Y) nA nB = just ((X ~ᶜ Y) ∷ [] , X-~-Y (here refl))
core-consistent? (＇ X) (｀ α) nA nB = nothing
core-consistent? (＇ X) (‵ ι) nA nB = nothing
core-consistent? (＇ X) ★ nA nB = just ((X ~ᶜ★) ∷ [] , νX-~-★ (here refl))
core-consistent? (＇ X) (B₁ ⇒ B₂) nA nB = nothing
core-consistent? (｀ α) B nA nB = nothing
core-consistent? (‵ ι) (＇ X) nA nB = nothing
core-consistent? (‵ ι) (｀ α) nA nB = nothing
core-consistent? (‵ ι) (‵ ι′) nA nB
    with ι ≟Base ι′
... | yes refl = just ([] , ι-~-ι)
... | no neq = nothing
core-consistent? (‵ ι) ★ nA nB = just ([] , ι-~-★)
core-consistent? (‵ ι) (B₁ ⇒ B₂) nA nB = nothing
core-consistent? ★ (＇ X) nA nB = just ((★~ᶜ X) ∷ [] , ★-~-νX (here refl))
core-consistent? ★ (｀ α) nA nB = nothing
core-consistent? ★ (‵ ι) nA nB = just ([] , ★-~-ι)
core-consistent? ★ ★ nA nB = just ([] , ★-~-★)
core-consistent? ★ (B₁ ⇒ B₂) nA nB
    with consistent? ★ B₁ | consistent? ★ B₂
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (Γ₁ , ★~B₁) | just (Γ₂ , ★~B₂)
    with consistent-ctx? Γ₁ Γ₂
... | true = just (Γ₁ ++ Γ₂ , ★-~-⇒ (wk-++ˡ ★~B₁) (wk-++ʳ Γ₁ ★~B₂))
... | false = nothing
core-consistent? (A₁ ⇒ A₂) (＇ X) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) (｀ α) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) (‵ ι) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) ★ nA nB
    with consistent? A₁ ★ | consistent? A₂ ★
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (Γ₁ , A₁~★) | just (Γ₂ , A₂~★)
    with consistent-ctx? Γ₁ Γ₂
... | true = just (Γ₁ ++ Γ₂ , ⇒-~-★ (wk-++ˡ A₁~★) (wk-++ʳ Γ₁ A₂~★))
... | false = nothing
core-consistent? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
    with consistent? A₁ B₁ | consistent? A₂ B₂
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (Γ₁ , A₁~A₂) | just (Γ₂ , B₁~B₂)
    with consistent-ctx? Γ₁ Γ₂
... | true = just (Γ₁ ++ Γ₂ , ⇒-~-⇒ (wk-++ˡ A₁~A₂) (wk-++ʳ Γ₁ B₁~B₂))
... | false = nothing

consistent? A B
    with split-∀ A in sA | split-∀ B in sB
... | n , A′ , n∀A | m , B′ , n∀B
    with core-consistent? A′ B′ n∀A n∀B
... | nothing = nothing
... | just (Γ , A′~B′)
    with lift-∀ n m A′~B′
...   | nothing = nothing
...   | just (Δ , A~B) =
        just (Δ , cast-right (split-add∀-from sB) (cast-left (split-add∀-from sA) A~B))


------------------------------------------------------------------------
-- Least Upper Bound, Greatest Lower Bound
------------------------------------------------------------------------
