module proof.ConsistencyAltProperties where

-- File Charter:
--   * Properties of type consistency.

open import Types
open import ImprecisionAlt
open import ConsistencyAlt
open import proof.ImprecisionAltProperties using
  ( no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; no-⇑ᴸᵢ-zero-star
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; un⇑ᴸᵢ-ˣ∈
  ; un⇑ᴸᵢ-★∈
  )

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; Dec)

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

clash : CAssm → CAssm → Bool
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) with X ≟ X′ | Y ≟ Y′
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | yes _ = false
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | yes _ | no _ = true
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | yes _ = true
clash (X ~ᶜ Y) (X′ ~ᶜ Y′) | no _ | no _ = false
clash _ _ = false

consistent-assm? : CAssm → CCtx → Bool
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

postulate
  wk-⊑-++ˡ :
    ∀ {Ψ Φ A B} (Γ : ImpCtx) →
    Ψ ∣ Φ ⊢ A ⊑ B →
    Ψ ∣ Φ ++ Γ ⊢ A ⊑ B

  wk-⊑-++ʳ :
    ∀ {Ψ Φ A B} (Γ : ImpCtx) →
    Ψ ∣ Φ ⊢ A ⊑ B →
    Ψ ∣ Γ ++ Φ ⊢ A ⊑ B

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

cast-⊑ : ∀ {Ψ Φ Φ′ A B} → Φ ≡ Φ′ → Ψ ∣ Φ ⊢ A ⊑ B → Ψ ∣ Φ′ ⊢ A ⊑ B
cast-⊑ refl A⊑B = A⊑B

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

unshiftₐ : (a : CAssm) → Maybe (Σ[ b ∈ CAssm ] ⇑ₐ b ≡ a)
unshiftₐ (suc X ~ᶜ★) = just (X ~ᶜ★ , refl)
unshiftₐ (★~ᶜ suc Y) = just (★~ᶜ Y , refl)
unshiftₐ (suc X ~ᶜ suc Y) = just (X ~ᶜ Y , refl)
unshiftₐ _ = nothing

unshiftᴸₐ : (a : CAssm) → Maybe (Σ[ b ∈ CAssm ] ⇑ᴸₐ b ≡ a)
unshiftᴸₐ (suc X ~ᶜ★) = just (X ~ᶜ★ , refl)
unshiftᴸₐ (★~ᶜ Y) = just (★~ᶜ Y , refl)
unshiftᴸₐ (suc X ~ᶜ Y) = just (X ~ᶜ Y , refl)
unshiftᴸₐ _ = nothing

unshiftᴿₐ : (a : CAssm) → Maybe (Σ[ b ∈ CAssm ] ⇑ᴿₐ b ≡ a)
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

{-# TERMINATING #-}
consistent? : (A B : Ty) → Maybe (Σ[ Γ ∈ CCtx ] Γ ⊢ A ~ B)

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
... | just (Γ₁ , ★~B₁) | just (Γ₂ , ★~B₂) =
      just (Γ₁ ++ Γ₂ , ★-~-⇒ (wk-++ˡ ★~B₁) (wk-++ʳ Γ₁ ★~B₂))
core-consistent? (A₁ ⇒ A₂) (＇ X) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) (｀ α) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) (‵ ι) nA nB = nothing
core-consistent? (A₁ ⇒ A₂) ★ nA nB
    with consistent? A₁ ★ | consistent? A₂ ★
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (Γ₁ , A₁~★) | just (Γ₂ , A₂~★) =
      just (Γ₁ ++ Γ₂ , ⇒-~-★ (wk-++ˡ A₁~★) (wk-++ʳ Γ₁ A₂~★))

core-consistent? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
    with consistent? A₁ B₁ | consistent? A₂ B₂
... | nothing | _ = nothing
... | _ | nothing = nothing
... | just (Γ₁ , A₁~A₂) | just (Γ₂ , B₁~B₂) =
      just (Γ₁ ++ Γ₂ , ⇒-~-⇒ (wk-++ˡ A₁~A₂) (wk-++ʳ Γ₁ B₁~B₂))


consistent? A B
    with split-∀ A in sA | split-∀ B in sB
... | n , A′ , n∀A | m , B′ , n∀B
    with core-consistent? A′ B′ n∀A n∀B
... | nothing = nothing
... | just (Γ , A′~B′)
    with lift-∀ n m A′~B′
...   | nothing = nothing
...   | just (Δ , A~B) =
        just (Δ , cast-right (split-add∀-from sB)
                    (cast-left (split-add∀-from sA) A~B))

------------------------------------------------------------------------
-- Consistency is exists Greatest Lower Bound
------------------------------------------------------------------------

⇑ᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (X ~ᶜ Y) ∈ Γ →
  (suc X ~ᶜ suc Y) ∈ ⇑ Γ
⇑ᶜ-ˣˣ∈ (here refl) = here refl
⇑ᶜ-ˣˣ∈ (there x~y) = there (⇑ᶜ-ˣˣ∈ x~y)

⇑ᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (X ~ᶜ★) ∈ Γ →
  (suc X ~ᶜ★) ∈ ⇑ Γ
⇑ᶜ-ˣ★∈ (here refl) = here refl
⇑ᶜ-ˣ★∈ (there x~★) = there (⇑ᶜ-ˣ★∈ x~★)

⇑ᶜ-★ˣ∈ :
  ∀ {Γ X} →
  (★~ᶜ X) ∈ Γ →
  (★~ᶜ suc X) ∈ ⇑ Γ
⇑ᶜ-★ˣ∈ (here refl) = here refl
⇑ᶜ-★ˣ∈ (there ★~x) = there (⇑ᶜ-★ˣ∈ ★~x)

⇑ᴸᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (X ~ᶜ Y) ∈ Γ →
  (suc X ~ᶜ Y) ∈ ⇑ᴸ Γ
⇑ᴸᶜ-ˣˣ∈ (here refl) = here refl
⇑ᴸᶜ-ˣˣ∈ (there x~y) = there (⇑ᴸᶜ-ˣˣ∈ x~y)

⇑ᴸᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (X ~ᶜ★) ∈ Γ →
  (suc X ~ᶜ★) ∈ ⇑ᴸ Γ
⇑ᴸᶜ-ˣ★∈ (here refl) = here refl
⇑ᴸᶜ-ˣ★∈ (there x~★) = there (⇑ᴸᶜ-ˣ★∈ x~★)

⇑ᴸᶜ-★ˣ∈ :
  ∀ {Γ X} →
  (★~ᶜ X) ∈ Γ →
  (★~ᶜ X) ∈ ⇑ᴸ Γ
⇑ᴸᶜ-★ˣ∈ (here refl) = here refl
⇑ᴸᶜ-★ˣ∈ (there ★~x) = there (⇑ᴸᶜ-★ˣ∈ ★~x)

⇑ᴿᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (X ~ᶜ Y) ∈ Γ →
  (X ~ᶜ suc Y) ∈ ⇑ᴿ Γ
⇑ᴿᶜ-ˣˣ∈ (here refl) = here refl
⇑ᴿᶜ-ˣˣ∈ (there x~y) = there (⇑ᴿᶜ-ˣˣ∈ x~y)

⇑ᴿᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (X ~ᶜ★) ∈ Γ →
  (X ~ᶜ★) ∈ ⇑ᴿ Γ
⇑ᴿᶜ-ˣ★∈ (here refl) = here refl
⇑ᴿᶜ-ˣ★∈ (there x~★) = there (⇑ᴿᶜ-ˣ★∈ x~★)

⇑ᴿᶜ-★ˣ∈ :
  ∀ {Γ X} →
  (★~ᶜ X) ∈ Γ →
  (★~ᶜ suc X) ∈ ⇑ᴿ Γ
⇑ᴿᶜ-★ˣ∈ (here refl) = here refl
⇑ᴿᶜ-★ˣ∈ (there ★~x) = there (⇑ᴿᶜ-★ˣ∈ ★~x)

record LowerCtx (Φᴸ Φᴿ : ImpCtx) (Γ : CCtx) : Set where
  field
    lower-var-var :
      ∀ {X Y Z} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (X ˣ⊑ˣ Z) ∈ Φᴿ →
      (Y ~ᶜ Z) ∈ Γ

    lower-var-star :
      ∀ {X Y} →
      (X ˣ⊑ˣ Y) ∈ Φᴸ →
      (X ˣ⊑★) ∈ Φᴿ →
      (Y ~ᶜ★) ∈ Γ

    lower-star-var :
      ∀ {X Z} →
      (X ˣ⊑★) ∈ Φᴸ →
      (X ˣ⊑ˣ Z) ∈ Φᴿ →
      (★~ᶜ Z) ∈ Γ

open LowerCtx public

LowerCtx-[] : LowerCtx [] [] []
LowerCtx-[] .lower-var-var ()
LowerCtx-[] .lower-var-star ()
LowerCtx-[] .lower-star-var ()

LowerCtx-νν :
  ∀ {Φᴸ Φᴿ Γ} →
  LowerCtx Φᴸ Φᴿ Γ →
  LowerCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ) ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ) Γ
LowerCtx-νν L .lower-var-var (here ()) _
LowerCtx-νν L .lower-var-var {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-νν L .lower-var-var {X = suc x} (there x⊑y) (here ())
LowerCtx-νν L .lower-var-var {X = suc x} (there x⊑y) (there x⊑z) =
  lower-var-var L (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-ˣ∈ x⊑z)
LowerCtx-νν L .lower-var-star (here ()) _
LowerCtx-νν L .lower-var-star {X = zero} (there x⊑y) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-νν L .lower-var-star {X = zero} (there x⊑y) (there x⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-νν L .lower-var-star {X = suc x} (there x⊑y) (there x⊑★) =
  lower-var-star L (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-★∈ x⊑★)
LowerCtx-νν L .lower-star-var (here refl) (here ())
LowerCtx-νν L .lower-star-var {X = zero} (here refl) (there x⊑z) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑z)
LowerCtx-νν L .lower-star-var {X = zero} (there x⊑★) (there x⊑z) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
LowerCtx-νν L .lower-star-var {X = suc x} (there x⊑★) (there x⊑z) =
  lower-star-var L (un⇑ᴸᵢ-★∈ x⊑★) (un⇑ᴸᵢ-ˣ∈ x⊑z)

LowerCtx-∀∀ :
  ∀ {Φᴸ Φᴿ Γ} →
  LowerCtx Φᴸ Φᴿ Γ →
  LowerCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ) ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
           ((0 ~ᶜ 0) ∷ ⇑ Γ)
LowerCtx-∀∀ L .lower-var-var (here refl) (here refl) = here refl
LowerCtx-∀∀ L .lower-var-var (here refl) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑z)
LowerCtx-∀∀ L .lower-var-var (there x⊑y) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
LowerCtx-∀∀ L .lower-var-var {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
LowerCtx-∀∀ L .lower-var-var {X = suc x} {Y = zero}
    (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
LowerCtx-∀∀ L .lower-var-var {X = suc x} {Z = zero}
    (there x⊑y) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑z)
LowerCtx-∀∀ L .lower-var-var {X = suc x} {Y = suc y} {Z = suc z}
    (there x⊑y) (there x⊑z) =
  there (⇑ᶜ-ˣˣ∈
    (lower-var-var L (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-ˣ∈ x⊑z)))
LowerCtx-∀∀ L .lower-var-star (here refl) (here ())
LowerCtx-∀∀ L .lower-var-star (here refl) (there x⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
LowerCtx-∀∀ L .lower-var-star {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
LowerCtx-∀∀ L .lower-var-star {X = suc x} {Y = zero}
    (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
LowerCtx-∀∀ L .lower-var-star {X = suc x} {Y = suc y}
    (there x⊑y) (there x⊑★) =
  there (⇑ᶜ-ˣ★∈
    (lower-var-star L (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ x⊑★)))
LowerCtx-∀∀ L .lower-star-var (here ()) (here refl)
LowerCtx-∀∀ L .lower-star-var (there x⊑★) (here refl) =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
LowerCtx-∀∀ L .lower-star-var {X = zero} (there x⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
LowerCtx-∀∀ L .lower-star-var {X = suc x} {Z = zero}
    (there x⊑★) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑z)
LowerCtx-∀∀ L .lower-star-var {X = suc x} {Z = suc z}
    (there x⊑★) (there x⊑z) =
  there (⇑ᶜ-★ˣ∈
    (lower-star-var L (un⇑ᵢ-★∈ x⊑★) (un⇑ᵢ-ˣ∈ x⊑z)))

LowerCtx-∀ν :
  ∀ {Φᴸ Φᴿ Γ} →
  LowerCtx Φᴸ Φᴿ Γ →
  LowerCtx ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ) ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
           ((0 ~ᶜ★) ∷ ⇑ᴸ Γ)
LowerCtx-∀ν L .lower-var-var (here refl) (here ())
LowerCtx-∀ν L .lower-var-var {X = zero} (here refl) (there x⊑z) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑z)
LowerCtx-∀ν L .lower-var-var {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
LowerCtx-∀ν L .lower-var-var {X = suc x} {Y = zero}
    (there x⊑y) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
LowerCtx-∀ν L .lower-var-var {X = suc x} {Y = suc y}
    (there x⊑y) (there x⊑z) =
  there (⇑ᴸᶜ-ˣˣ∈
    (lower-var-var L (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-ˣ∈ x⊑z)))
LowerCtx-∀ν L .lower-var-star (here refl) (here refl) = here refl
LowerCtx-∀ν L .lower-var-star (here refl) (there x⊑★) =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
LowerCtx-∀ν L .lower-var-star {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑y)
LowerCtx-∀ν L .lower-var-star {X = suc x} {Y = zero}
    (there x⊑y) (there x⊑★) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑y)
LowerCtx-∀ν L .lower-var-star {X = suc x} {Y = suc y}
    (there x⊑y) (there x⊑★) =
  there (⇑ᴸᶜ-ˣ★∈
    (lower-var-star L (un⇑ᵢ-ˣ∈ x⊑y) (un⇑ᴸᵢ-★∈ x⊑★)))
LowerCtx-∀ν L .lower-star-var {X = zero} (here ()) _
LowerCtx-∀ν L .lower-star-var {X = zero} (there x⊑★) _ =
  ⊥-elim (no-⇑ᵢ-zero-star x⊑★)
LowerCtx-∀ν L .lower-star-var {X = suc x} (there x⊑★) (here ())
LowerCtx-∀ν L .lower-star-var {X = suc x} (there x⊑★) (there x⊑z) =
  there (⇑ᴸᶜ-★ˣ∈
    (lower-star-var L (un⇑ᵢ-★∈ x⊑★) (un⇑ᴸᵢ-ˣ∈ x⊑z)))

LowerCtx-ν∀ :
  ∀ {Φᴸ Φᴿ Γ} →
  LowerCtx Φᴸ Φᴿ Γ →
  LowerCtx ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ) ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
           ((★~ᶜ 0) ∷ ⇑ᴿ Γ)
LowerCtx-ν∀ L .lower-var-var (here ()) _
LowerCtx-ν∀ L .lower-var-var (there x⊑y) (here refl) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-ν∀ L .lower-var-var {X = zero} (there x⊑y) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-ν∀ L .lower-var-var {X = suc x} {Z = zero}
    (there x⊑y) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑z)
LowerCtx-ν∀ L .lower-var-var {X = suc x} {Z = suc z}
    (there x⊑y) (there x⊑z) =
  there (⇑ᴿᶜ-ˣˣ∈
    (lower-var-var L (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᵢ-ˣ∈ x⊑z)))
LowerCtx-ν∀ L .lower-var-star (here ()) _
LowerCtx-ν∀ L .lower-var-star {X = zero} (there x⊑y) x⊑★ =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑y)
LowerCtx-ν∀ L .lower-var-star {X = suc x} (there x⊑y) (there x⊑★) =
  there (⇑ᴿᶜ-ˣ★∈
    (lower-var-star L (un⇑ᴸᵢ-ˣ∈ x⊑y) (un⇑ᵢ-★∈ x⊑★)))
LowerCtx-ν∀ L .lower-star-var (here refl) (here refl) = here refl
LowerCtx-ν∀ L .lower-star-var (here refl) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-left x⊑z)
LowerCtx-ν∀ L .lower-star-var {X = zero} (there x⊑★) _ =
  ⊥-elim (no-⇑ᴸᵢ-zero-star x⊑★)
LowerCtx-ν∀ L .lower-star-var {X = suc x} {Z = zero}
    (there x⊑★) (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑z)
LowerCtx-ν∀ L .lower-star-var {X = suc x} {Z = suc z}
    (there x⊑★) (there x⊑z) =
  there (⇑ᴿᶜ-★ˣ∈
    (lower-star-var L (un⇑ᴸᵢ-★∈ x⊑★) (un⇑ᵢ-ˣ∈ x⊑z)))
