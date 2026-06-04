module proof.ConsistencyAltProperties where

-- File Charter:
--   * Properties of type consistency.

open import Types
open import ImprecisionAlt
open import ConsistencyAlt
open import proof.ImprecisionAltProperties using
  ( GlbCtx
  ; GlbCtx-[]
  ; Glbᶜ
  ; glbᶜ-base-base
  ; glbᶜ-base-star
  ; glbᶜ-closed⇒⊓
  ; glbᶜ-intro
  ; glbᶜ-lift-∀∀-open
  ; glbᶜ-lift-∀ν-open
  ; glbᶜ-lift-ν∀-open
  ; glbᶜ-star-base
  ; glbᶜ-star-star
  ; glbᶜ-star-var
  ; glbᶜ-var-star
  ; glbᶜ-var-var
  ; glb-star-star
  ; glb-star-var
  ; glb-var-star
  ; glb-var-var
  ; greatest-star-varᵍ
  ; greatest-var-starᵍ
  ; greatest-var-varᵍ
  ; lowerʳᶜ
  ; lowerˡᶜ
  ; no-⇑ᵢ-zero-left
  ; no-⇑ᵢ-zero-right
  ; no-⇑ᵢ-zero-star
  ; no-⇑ᴸᵢ-zero-left
  ; no-⇑ᴸᵢ-zero-star
  ; ⇑ᵢ-ˣ∈
  ; ⇑ᵢ-★∈
  ; ⇑ᴸᵢ-ˣ∈
  ; ⇑ᴸᵢ-★∈
  ; plainν-target-occurs-source
  ; un⇑ᵢ-ˣ∈
  ; un⇑ᵢ-★∈
  ; un⇑ᴸᵢ-ˣ∈
  ; un⇑ᴸᵢ-★∈
  )

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
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

unshiftᵢₐ : (a : ImpAssm) → Maybe (Σ[ b ∈ ImpAssm ] ⇑ᵢₐ b ≡ a)
unshiftᵢₐ (suc X ˣ⊑★) = just (X ˣ⊑★ , refl)
unshiftᵢₐ (suc X ˣ⊑ˣ suc Y) = just (X ˣ⊑ˣ Y , refl)
unshiftᵢₐ _ = nothing

unshiftᴸᵢₐ : (a : ImpAssm) → Maybe (Σ[ b ∈ ImpAssm ] ⇑ᴸᵢₐ b ≡ a)
unshiftᴸᵢₐ (suc X ˣ⊑★) = just (X ˣ⊑★ , refl)
unshiftᴸᵢₐ (suc X ˣ⊑ˣ Y) = just (X ˣ⊑ˣ Y , refl)
unshiftᴸᵢₐ _ = nothing

unshiftᵢ : (Φ : ImpCtx) → Maybe (Σ[ Δ ∈ ImpCtx ] ⇑ᵢ Δ ≡ Φ)
unshiftᵢ [] = just ([] , refl)
unshiftᵢ (a ∷ Φ)
    with unshiftᵢₐ a | unshiftᵢ Φ
unshiftᵢ (a ∷ Φ) | nothing | _ = nothing
unshiftᵢ (a ∷ Φ) | _ | nothing = nothing
unshiftᵢ (a ∷ Φ) | just (b , eq₁) | just (Δ , eq₂) =
  just (b ∷ Δ , trans (cong (λ xs → ⇑ᵢₐ b ∷ xs) eq₂)
                       (cong (λ x → x ∷ Φ) eq₁))

unshiftᴸᵢ : (Φ : ImpCtx) → Maybe (Σ[ Δ ∈ ImpCtx ] ⇑ᴸᵢ Δ ≡ Φ)
unshiftᴸᵢ [] = just ([] , refl)
unshiftᴸᵢ (a ∷ Φ)
    with unshiftᴸᵢₐ a | unshiftᴸᵢ Φ
unshiftᴸᵢ (a ∷ Φ) | nothing | _ = nothing
unshiftᴸᵢ (a ∷ Φ) | _ | nothing = nothing
unshiftᴸᵢ (a ∷ Φ) | just (b , eq₁) | just (Δ , eq₂) =
  just (b ∷ Δ , trans (cong (λ xs → ⇑ᴸᵢₐ b ∷ xs) eq₂)
                       (cong (λ x → x ∷ Φ) eq₁))

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

un⇑ᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (suc X ~ᶜ suc Y) ∈ ⇑ Γ →
  (X ~ᶜ Y) ∈ Γ
un⇑ᶜ-ˣˣ∈ {Γ = []} ()
un⇑ᶜ-ˣˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  there (un⇑ᶜ-ˣˣ∈ x~y)
un⇑ᶜ-ˣˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᶜ-ˣˣ∈ x~y)
un⇑ᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᶜ-ˣˣ∈ x~y)

un⇑ᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (suc X ~ᶜ★) ∈ ⇑ Γ →
  (X ~ᶜ★) ∈ Γ
un⇑ᶜ-ˣ★∈ {Γ = []} ()
un⇑ᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
un⇑ᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~★) =
  there (un⇑ᶜ-ˣ★∈ x~★)
un⇑ᶜ-ˣ★∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᶜ-ˣ★∈ x~★)
un⇑ᶜ-ˣ★∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᶜ-ˣ★∈ x~★)

un⇑ᶜ-★ˣ∈ :
  ∀ {Γ Y} →
  (★~ᶜ suc Y) ∈ ⇑ Γ →
  (★~ᶜ Y) ∈ Γ
un⇑ᶜ-★ˣ∈ {Γ = []} ()
un⇑ᶜ-★ˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there ★~y) =
  there (un⇑ᶜ-★ˣ∈ ★~y)
un⇑ᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᶜ-★ˣ∈ ★~y)
un⇑ᶜ-★ˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᶜ-★ˣ∈ ★~y)

no-⇑ᶜ-zero-left :
  ∀ {Γ Y} →
  (zero ~ᶜ Y) ∈ ⇑ Γ →
  ⊥
no-⇑ᶜ-zero-left {Γ = []} ()
no-⇑ᶜ-zero-left {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-left x~y
no-⇑ᶜ-zero-left {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-left x~y
no-⇑ᶜ-zero-left {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-left x~y

no-⇑ᶜ-zero-right :
  ∀ {Γ X} →
  (X ~ᶜ zero) ∈ ⇑ Γ →
  ⊥
no-⇑ᶜ-zero-right {Γ = []} ()
no-⇑ᶜ-zero-right {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-right x~y
no-⇑ᶜ-zero-right {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-right x~y
no-⇑ᶜ-zero-right {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᶜ-zero-right x~y

no-⇑ᶜ-zero-star :
  ∀ {Γ} →
  (zero ~ᶜ★) ∈ ⇑ Γ →
  ⊥
no-⇑ᶜ-zero-star {Γ = []} ()
no-⇑ᶜ-zero-star {Γ = (_ ~ᶜ★) ∷ Γ} (there x~★) =
  no-⇑ᶜ-zero-star x~★
no-⇑ᶜ-zero-star {Γ = (★~ᶜ _) ∷ Γ} (there x~★) =
  no-⇑ᶜ-zero-star x~★
no-⇑ᶜ-zero-star {Γ = (_ ~ᶜ _) ∷ Γ} (there x~★) =
  no-⇑ᶜ-zero-star x~★

no-⇑ᶜ-star-zero :
  ∀ {Γ} →
  (★~ᶜ zero) ∈ ⇑ Γ →
  ⊥
no-⇑ᶜ-star-zero {Γ = []} ()
no-⇑ᶜ-star-zero {Γ = (_ ~ᶜ★) ∷ Γ} (there ★~x) =
  no-⇑ᶜ-star-zero ★~x
no-⇑ᶜ-star-zero {Γ = (★~ᶜ _) ∷ Γ} (there ★~x) =
  no-⇑ᶜ-star-zero ★~x
no-⇑ᶜ-star-zero {Γ = (_ ~ᶜ _) ∷ Γ} (there ★~x) =
  no-⇑ᶜ-star-zero ★~x

un⇑ᴸᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (suc X ~ᶜ Y) ∈ ⇑ᴸ Γ →
  (X ~ᶜ Y) ∈ Γ
un⇑ᴸᶜ-ˣˣ∈ {Γ = []} ()
un⇑ᴸᶜ-ˣˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  there (un⇑ᴸᶜ-ˣˣ∈ x~y)
un⇑ᴸᶜ-ˣˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᴸᶜ-ˣˣ∈ x~y)
un⇑ᴸᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᴸᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᴸᶜ-ˣˣ∈ x~y)

un⇑ᴸᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (suc X ~ᶜ★) ∈ ⇑ᴸ Γ →
  (X ~ᶜ★) ∈ Γ
un⇑ᴸᶜ-ˣ★∈ {Γ = []} ()
un⇑ᴸᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
un⇑ᴸᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~★) =
  there (un⇑ᴸᶜ-ˣ★∈ x~★)
un⇑ᴸᶜ-ˣ★∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᴸᶜ-ˣ★∈ x~★)
un⇑ᴸᶜ-ˣ★∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᴸᶜ-ˣ★∈ x~★)

un⇑ᴸᶜ-★ˣ∈ :
  ∀ {Γ Y} →
  (★~ᶜ Y) ∈ ⇑ᴸ Γ →
  (★~ᶜ Y) ∈ Γ
un⇑ᴸᶜ-★ˣ∈ {Γ = []} ()
un⇑ᴸᶜ-★ˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there ★~y) =
  there (un⇑ᴸᶜ-★ˣ∈ ★~y)
un⇑ᴸᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᴸᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᴸᶜ-★ˣ∈ ★~y)
un⇑ᴸᶜ-★ˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᴸᶜ-★ˣ∈ ★~y)

no-⇑ᴸᶜ-zero-left :
  ∀ {Γ Y} →
  (zero ~ᶜ Y) ∈ ⇑ᴸ Γ →
  ⊥
no-⇑ᴸᶜ-zero-left {Γ = []} ()
no-⇑ᴸᶜ-zero-left {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  no-⇑ᴸᶜ-zero-left x~y
no-⇑ᴸᶜ-zero-left {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᴸᶜ-zero-left x~y
no-⇑ᴸᶜ-zero-left {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᴸᶜ-zero-left x~y

no-⇑ᴸᶜ-zero-star :
  ∀ {Γ} →
  (zero ~ᶜ★) ∈ ⇑ᴸ Γ →
  ⊥
no-⇑ᴸᶜ-zero-star {Γ = []} ()
no-⇑ᴸᶜ-zero-star {Γ = (_ ~ᶜ★) ∷ Γ} (there x~★) =
  no-⇑ᴸᶜ-zero-star x~★
no-⇑ᴸᶜ-zero-star {Γ = (★~ᶜ _) ∷ Γ} (there x~★) =
  no-⇑ᴸᶜ-zero-star x~★
no-⇑ᴸᶜ-zero-star {Γ = (_ ~ᶜ _) ∷ Γ} (there x~★) =
  no-⇑ᴸᶜ-zero-star x~★

un⇑ᴿᶜ-ˣˣ∈ :
  ∀ {Γ X Y} →
  (X ~ᶜ suc Y) ∈ ⇑ᴿ Γ →
  (X ~ᶜ Y) ∈ Γ
un⇑ᴿᶜ-ˣˣ∈ {Γ = []} ()
un⇑ᴿᶜ-ˣˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  there (un⇑ᴿᶜ-ˣˣ∈ x~y)
un⇑ᴿᶜ-ˣˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᴿᶜ-ˣˣ∈ x~y)
un⇑ᴿᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᴿᶜ-ˣˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  there (un⇑ᴿᶜ-ˣˣ∈ x~y)

un⇑ᴿᶜ-ˣ★∈ :
  ∀ {Γ X} →
  (X ~ᶜ★) ∈ ⇑ᴿ Γ →
  (X ~ᶜ★) ∈ Γ
un⇑ᴿᶜ-ˣ★∈ {Γ = []} ()
un⇑ᴿᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (here refl) = here refl
un⇑ᴿᶜ-ˣ★∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there x~★) =
  there (un⇑ᴿᶜ-ˣ★∈ x~★)
un⇑ᴿᶜ-ˣ★∈ {Γ = (★~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᴿᶜ-ˣ★∈ x~★)
un⇑ᴿᶜ-ˣ★∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there x~★) =
  there (un⇑ᴿᶜ-ˣ★∈ x~★)

un⇑ᴿᶜ-★ˣ∈ :
  ∀ {Γ Y} →
  (★~ᶜ suc Y) ∈ ⇑ᴿ Γ →
  (★~ᶜ Y) ∈ Γ
un⇑ᴿᶜ-★ˣ∈ {Γ = []} ()
un⇑ᴿᶜ-★ˣ∈ {Γ = (_ ~ᶜ★) ∷ Γ} (there ★~y) =
  there (un⇑ᴿᶜ-★ˣ∈ ★~y)
un⇑ᴿᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (here refl) = here refl
un⇑ᴿᶜ-★ˣ∈ {Γ = (★~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᴿᶜ-★ˣ∈ ★~y)
un⇑ᴿᶜ-★ˣ∈ {Γ = (_ ~ᶜ _) ∷ Γ} (there ★~y) =
  there (un⇑ᴿᶜ-★ˣ∈ ★~y)

no-⇑ᴿᶜ-zero-right :
  ∀ {Γ X} →
  (X ~ᶜ zero) ∈ ⇑ᴿ Γ →
  ⊥
no-⇑ᴿᶜ-zero-right {Γ = []} ()
no-⇑ᴿᶜ-zero-right {Γ = (_ ~ᶜ★) ∷ Γ} (there x~y) =
  no-⇑ᴿᶜ-zero-right x~y
no-⇑ᴿᶜ-zero-right {Γ = (★~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᴿᶜ-zero-right x~y
no-⇑ᴿᶜ-zero-right {Γ = (_ ~ᶜ _) ∷ Γ} (there x~y) =
  no-⇑ᴿᶜ-zero-right x~y

no-⇑ᴿᶜ-star-zero :
  ∀ {Γ} →
  (★~ᶜ zero) ∈ ⇑ᴿ Γ →
  ⊥
no-⇑ᴿᶜ-star-zero {Γ = []} ()
no-⇑ᴿᶜ-star-zero {Γ = (_ ~ᶜ★) ∷ Γ} (there ★~x) =
  no-⇑ᴿᶜ-star-zero ★~x
no-⇑ᴿᶜ-star-zero {Γ = (★~ᶜ _) ∷ Γ} (there ★~x) =
  no-⇑ᴿᶜ-star-zero ★~x
no-⇑ᴿᶜ-star-zero {Γ = (_ ~ᶜ _) ∷ Γ} (there ★~x) =
  no-⇑ᴿᶜ-star-zero ★~x

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

false≢true : false ≡ true → ⊥
false≢true ()

∨-trueˡ :
  ∀ {b c} →
  b ≡ true →
  b ∨ c ≡ true
∨-trueˡ {b = true} refl = refl
∨-trueˡ {b = false} ()

∨-trueʳ :
  ∀ {b c} →
  c ≡ true →
  b ∨ c ≡ true
∨-trueʳ {b = true} refl = refl
∨-trueʳ {b = false} eq = eq

occurs-same : ∀ X → occurs X (＇ X) ≡ true
occurs-same X with X ≟ X
... | yes refl = refl
... | no neq = ⊥-elim (neq refl)

record SourceFocus (Φ : ImpCtx) (X Y : TyVar) : Set where
  field
    hitˢ : (X ˣ⊑ˣ Y) ∈ Φ
    unique-target : ∀ {Z} → (X ˣ⊑ˣ Z) ∈ Φ → Z ≡ Y
    no-star-target : (X ˣ⊑★) ∈ Φ → ⊥

open SourceFocus public

source-focus-plain-zero :
  ∀ {Φ} →
  SourceFocus ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) 0 0
source-focus-plain-zero .hitˢ = here refl
source-focus-plain-zero .unique-target (here refl) = refl
source-focus-plain-zero .unique-target (there z⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-left z⊑0)
source-focus-plain-zero .no-star-target (here ())
source-focus-plain-zero .no-star-target (there z⊑★) =
  no-⇑ᵢ-zero-star z⊑★

source-focus-∀ :
  ∀ {Φ X Y} →
  SourceFocus Φ X Y →
  SourceFocus ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) (suc X) (suc Y)
source-focus-∀ f .hitˢ = there (⇑ᵢ-ˣ∈ (hitˢ f))
source-focus-∀ f .unique-target (here ())
source-focus-∀ f .unique-target {Z = zero} (there x⊑z) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑z)
source-focus-∀ f .unique-target {Z = suc z} (there x⊑z)
  rewrite unique-target f (un⇑ᵢ-ˣ∈ x⊑z) =
  refl
source-focus-∀ f .no-star-target (here ())
source-focus-∀ f .no-star-target (there x⊑★) =
  no-star-target f (un⇑ᵢ-★∈ x⊑★)

source-focus-ν :
  ∀ {Φ X Y} →
  SourceFocus Φ X Y →
  SourceFocus ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc X) Y
source-focus-ν f .hitˢ = there (⇑ᴸᵢ-ˣ∈ (hitˢ f))
source-focus-ν f .unique-target (here ())
source-focus-ν f .unique-target (there x⊑z)
  rewrite unique-target f (un⇑ᴸᵢ-ˣ∈ x⊑z) =
  refl
source-focus-ν f .no-star-target (here ())
source-focus-ν f .no-star-target (there x⊑★) =
  no-star-target f (un⇑ᴸᵢ-★∈ x⊑★)

source-occurs-target-focus :
  ∀ {Ψ Φ X Y A B} →
  SourceFocus Φ X Y →
  Ψ ∣ Φ ⊢ A ⊑ B →
  occurs X A ≡ true →
  occurs Y B ≡ true
source-occurs-target-focus f id★ ()
source-occurs-target-focus {X = X} {Y = Y} f
    (idˣ {X = X′} {Y = Y′} x′⊑y′) occ
    with X ≟ X′
... | yes refl
    rewrite unique-target f x′⊑y′ =
  occurs-same Y
... | no neq = ⊥-elim (false≢true occ)
source-occurs-target-focus f idι ()
source-occurs-target-focus f (idα wfα) ()
source-occurs-target-focus {X = X} f
    (_↦_ {A = A} {B = B} p q) occ
    with occurs X A in occA
... | true = ∨-trueˡ (source-occurs-target-focus f p occA)
... | false = ∨-trueʳ (source-occurs-target-focus f q occ)
source-occurs-target-focus f (∀ⁱ p) occ =
  source-occurs-target-focus (source-focus-∀ f) p occ
source-occurs-target-focus f (tag ι) ()
source-occurs-target-focus {X = X} f
    (tag_⇒_ {A₁ = A₁} {A₂ = A₂} p q) occ
    with occurs X A₁ in occA₁
... | true =
  ⊥-elim (false≢true (source-occurs-target-focus f p occA₁))
... | false =
  ⊥-elim (false≢true (source-occurs-target-focus f q occ))
source-occurs-target-focus {X = X} {A = ＇ X′} f (tagˣ x⊑★) occ
    with X ≟ X′
... | yes refl = ⊥-elim (no-star-target f x⊑★)
... | no neq = ⊥-elim (false≢true occ)
source-occurs-target-focus f (ν occA p) occ =
  source-occurs-target-focus (source-focus-ν f) p occ

plain-source-occurs-target :
  ∀ {Ψ Φ A B} →
  Ψ ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ ⊢ A ⊑ B →
  occurs zero A ≡ true →
  occurs zero B ≡ true
plain-source-occurs-target =
  source-occurs-target-focus source-focus-plain-zero

lower-bounds-consistentᶜ :
  ∀ {Φᴸ Φᴿ Γ A B C} →
  LowerCtx Φᴸ Φᴿ Γ →
  0 ∣ Φᴸ ⊢ A ⊑ B →
  0 ∣ Φᴿ ⊢ A ⊑ C →
  Γ ⊢ B ~ C
lower-bounds-consistentᶜ L id★ id★ = ★-~-★
lower-bounds-consistentᶜ L (idˣ x⊑y) (idˣ x⊑z) =
  X-~-Y (lower-var-var L x⊑y x⊑z)
lower-bounds-consistentᶜ L (idˣ x⊑y) (tagˣ x⊑★) =
  νX-~-★ (lower-var-star L x⊑y x⊑★)
lower-bounds-consistentᶜ L idι idι = ι-~-ι
lower-bounds-consistentᶜ L idι (tag ι) = ι-~-★
lower-bounds-consistentᶜ L (idα (wfSeal ())) q
lower-bounds-consistentᶜ L (p₁ ↦ p₂) (q₁ ↦ q₂) =
  ⇒-~-⇒ (lower-bounds-consistentᶜ L p₁ q₁)
         (lower-bounds-consistentᶜ L p₂ q₂)
lower-bounds-consistentᶜ L (p₁ ↦ p₂) (tag_⇒_ q₁ q₂) =
  ⇒-~-★ (lower-bounds-consistentᶜ L p₁ q₁)
         (lower-bounds-consistentᶜ L p₂ q₂)
lower-bounds-consistentᶜ L (∀ⁱ p) (∀ⁱ q) =
  ∀-~-∀ (lower-bounds-consistentᶜ (LowerCtx-∀∀ L) p q)
lower-bounds-consistentᶜ L (∀ⁱ p) (ν occA q) =
  ∀-~-B (plain-source-occurs-target p occA)
    (lower-bounds-consistentᶜ (LowerCtx-∀ν L) p q)
lower-bounds-consistentᶜ L (tag ι) idι = ★-~-ι
lower-bounds-consistentᶜ L (tag ι) (tag ι) = ★-~-★
lower-bounds-consistentᶜ L (tag_⇒_ p₁ p₂) (q₁ ↦ q₂) =
  ★-~-⇒ (lower-bounds-consistentᶜ L p₁ q₁)
         (lower-bounds-consistentᶜ L p₂ q₂)
lower-bounds-consistentᶜ L (tag_⇒_ p₁ p₂) (tag_⇒_ q₁ q₂) = ★-~-★
lower-bounds-consistentᶜ L (tagˣ x⊑★) (idˣ x⊑z) =
  ★-~-νX (lower-star-var L x⊑★ x⊑z)
lower-bounds-consistentᶜ L (tagˣ x⊑★) (tagˣ x⊑★′) = ★-~-★
lower-bounds-consistentᶜ L (ν occA p) (∀ⁱ q) =
  A-~-∀ (plain-source-occurs-target q occA)
    (lower-bounds-consistentᶜ (LowerCtx-ν∀ L) p q)
lower-bounds-consistentᶜ L (ν occA p) (ν occA′ q) =
  lower-bounds-consistentᶜ (LowerCtx-νν L) p q

lower-bounds-consistent :
  ∀ {A B C} →
  0 ∣ [] ⊢ A ⊑ B →
  0 ∣ [] ⊢ A ⊑ C →
  [] ⊢ B ~ C
lower-bounds-consistent =
  lower-bounds-consistentᶜ LowerCtx-[]

record BoundsCtx (Γ : CCtx) (Φᴸ Φᴿ : ImpCtx) : Set where
  field
    bounds-var-var :
      ∀ {X Y} →
      (X ~ᶜ Y) ∈ Γ →
      Σ[ Z ∈ TyVar ] ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ)

    bounds-var-star :
      ∀ {X} →
      (X ~ᶜ★) ∈ Γ →
      Σ[ Z ∈ TyVar ] ((Z ˣ⊑ˣ X) ∈ Φᴸ × (Z ˣ⊑★) ∈ Φᴿ)

    bounds-star-var :
      ∀ {Y} →
      (★~ᶜ Y) ∈ Γ →
      Σ[ Z ∈ TyVar ] ((Z ˣ⊑★) ∈ Φᴸ × (Z ˣ⊑ˣ Y) ∈ Φᴿ)

open BoundsCtx public

BoundsCtx-[] : BoundsCtx [] [] []
BoundsCtx-[] .bounds-var-var ()
BoundsCtx-[] .bounds-var-star ()
BoundsCtx-[] .bounds-star-var ()

BoundsCtx-∀∀ :
  ∀ {Γ Φᴸ Φᴿ} →
  BoundsCtx Γ Φᴸ Φᴿ →
  BoundsCtx ((0 ~ᶜ 0) ∷ ⇑ Γ)
            ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
            ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
BoundsCtx-∀∀ B .bounds-var-var (here refl) =
  zero , here refl , here refl
BoundsCtx-∀∀ B .bounds-var-var {X = zero} (there x~y) =
  ⊥-elim (no-⇑ᶜ-zero-left x~y)
BoundsCtx-∀∀ B .bounds-var-var {X = suc x} {Y = zero} (there x~y) =
  ⊥-elim (no-⇑ᶜ-zero-right x~y)
BoundsCtx-∀∀ B .bounds-var-var {X = suc x} {Y = suc y} (there x~y)
    with bounds-var-var B (un⇑ᶜ-ˣˣ∈ x~y)
... | z , z⊑x , z⊑y =
      suc z , there (⇑ᵢ-ˣ∈ z⊑x) , there (⇑ᵢ-ˣ∈ z⊑y)
BoundsCtx-∀∀ B .bounds-var-star {X = zero} (there x~★) =
  ⊥-elim (no-⇑ᶜ-zero-star x~★)
BoundsCtx-∀∀ B .bounds-var-star {X = suc x} (there x~★)
    with bounds-var-star B (un⇑ᶜ-ˣ★∈ x~★)
... | z , z⊑x , z⊑★ =
      suc z , there (⇑ᵢ-ˣ∈ z⊑x) , there (⇑ᵢ-★∈ z⊑★)
BoundsCtx-∀∀ B .bounds-star-var {Y = zero} (there ★~y) =
  ⊥-elim (no-⇑ᶜ-star-zero ★~y)
BoundsCtx-∀∀ B .bounds-star-var {Y = suc y} (there ★~y)
    with bounds-star-var B (un⇑ᶜ-★ˣ∈ ★~y)
... | z , z⊑★ , z⊑y =
      suc z , there (⇑ᵢ-★∈ z⊑★) , there (⇑ᵢ-ˣ∈ z⊑y)

BoundsCtx-∀ν :
  ∀ {Γ Φᴸ Φᴿ} →
  BoundsCtx Γ Φᴸ Φᴿ →
  BoundsCtx ((0 ~ᶜ★) ∷ ⇑ᴸ Γ)
            ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
            ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
BoundsCtx-∀ν B .bounds-var-var (here ())
BoundsCtx-∀ν B .bounds-var-var {X = zero} (there x~y) =
  ⊥-elim (no-⇑ᴸᶜ-zero-left x~y)
BoundsCtx-∀ν B .bounds-var-var {X = suc x} (there x~y)
    with bounds-var-var B (un⇑ᴸᶜ-ˣˣ∈ x~y)
... | z , z⊑x , z⊑y =
      suc z , there (⇑ᵢ-ˣ∈ z⊑x) , there (⇑ᴸᵢ-ˣ∈ z⊑y)
BoundsCtx-∀ν B .bounds-var-star (here refl) =
  zero , here refl , here refl
BoundsCtx-∀ν B .bounds-var-star {X = zero} (there x~★) =
  ⊥-elim (no-⇑ᴸᶜ-zero-star x~★)
BoundsCtx-∀ν B .bounds-var-star {X = suc x} (there x~★)
    with bounds-var-star B (un⇑ᴸᶜ-ˣ★∈ x~★)
... | z , z⊑x , z⊑★ =
      suc z , there (⇑ᵢ-ˣ∈ z⊑x) , there (⇑ᴸᵢ-★∈ z⊑★)
BoundsCtx-∀ν B .bounds-star-var (here ())
BoundsCtx-∀ν B .bounds-star-var (there ★~y)
    with bounds-star-var B (un⇑ᴸᶜ-★ˣ∈ ★~y)
... | z , z⊑★ , z⊑y =
      suc z , there (⇑ᵢ-★∈ z⊑★) , there (⇑ᴸᵢ-ˣ∈ z⊑y)

BoundsCtx-ν∀ :
  ∀ {Γ Φᴸ Φᴿ} →
  BoundsCtx Γ Φᴸ Φᴿ →
  BoundsCtx ((★~ᶜ 0) ∷ ⇑ᴿ Γ)
            ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
            ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
BoundsCtx-ν∀ B .bounds-var-var (here ())
BoundsCtx-ν∀ B .bounds-var-var {Y = zero} (there x~y) =
  ⊥-elim (no-⇑ᴿᶜ-zero-right x~y)
BoundsCtx-ν∀ B .bounds-var-var {Y = suc y} (there x~y)
    with bounds-var-var B (un⇑ᴿᶜ-ˣˣ∈ x~y)
... | z , z⊑x , z⊑y =
      suc z , there (⇑ᴸᵢ-ˣ∈ z⊑x) , there (⇑ᵢ-ˣ∈ z⊑y)
BoundsCtx-ν∀ B .bounds-var-star (here ())
BoundsCtx-ν∀ B .bounds-var-star (there x~★)
    with bounds-var-star B (un⇑ᴿᶜ-ˣ★∈ x~★)
... | z , z⊑x , z⊑★ =
      suc z , there (⇑ᴸᵢ-ˣ∈ z⊑x) , there (⇑ᵢ-★∈ z⊑★)
BoundsCtx-ν∀ B .bounds-star-var (here refl) =
  zero , here refl , here refl
BoundsCtx-ν∀ B .bounds-star-var {Y = zero} (there ★~y) =
  ⊥-elim (no-⇑ᴿᶜ-star-zero ★~y)
BoundsCtx-ν∀ B .bounds-star-var {Y = suc y} (there ★~y)
    with bounds-star-var B (un⇑ᴿᶜ-★ˣ∈ ★~y)
... | z , z⊑★ , z⊑y =
      suc z , there (⇑ᴸᵢ-★∈ z⊑★) , there (⇑ᵢ-ˣ∈ z⊑y)

consistent-common-lowerᶜ :
  ∀ {Γ Φᴸ Φᴿ A B} →
  BoundsCtx Γ Φᴸ Φᴿ →
  Γ ⊢ A ~ B →
  Σ[ C ∈ Ty ] CommonLowerᶜ Φᴸ Φᴿ C A B
consistent-common-lowerᶜ B ★-~-★ = ★ , id★ , id★
consistent-common-lowerᶜ B (X-~-Y x~y)
    with bounds-var-var B x~y
... | z , z⊑x , z⊑y = ＇ z , idˣ z⊑x , idˣ z⊑y
consistent-common-lowerᶜ B ι-~-ι = ‵ _ , idι , idι
consistent-common-lowerᶜ B (⇒-~-⇒ A~A′ B~B′)
    with consistent-common-lowerᶜ B A~A′
       | consistent-common-lowerᶜ B B~B′
... | Aₘ , Aₘ⊑A , Aₘ⊑A′ | Bₘ , Bₘ⊑B , Bₘ⊑B′ =
      Aₘ ⇒ Bₘ , Aₘ⊑A ↦ Bₘ⊑B , Aₘ⊑A′ ↦ Bₘ⊑B′
consistent-common-lowerᶜ B (∀-~-∀ A~B)
    with consistent-common-lowerᶜ (BoundsCtx-∀∀ B) A~B
... | C , C⊑A , C⊑B = `∀ C , ∀ⁱ C⊑A , ∀ⁱ C⊑B
consistent-common-lowerᶜ B ι-~-★ = ‵ _ , idι , tag _
consistent-common-lowerᶜ B (⇒-~-★ A₁~★ A₂~★)
    with consistent-common-lowerᶜ B A₁~★
       | consistent-common-lowerᶜ B A₂~★
... | C₁ , C₁⊑A₁ , C₁⊑★ | C₂ , C₂⊑A₂ , C₂⊑★ =
      C₁ ⇒ C₂ , C₁⊑A₁ ↦ C₂⊑A₂ , tag_⇒_ C₁⊑★ C₂⊑★
consistent-common-lowerᶜ B (νX-~-★ x~★)
    with bounds-var-star B x~★
... | z , z⊑x , z⊑★ = ＇ z , idˣ z⊑x , tagˣ z⊑★
consistent-common-lowerᶜ B ★-~-ι = ‵ _ , tag _ , idι
consistent-common-lowerᶜ B (★-~-⇒ ★~B₁ ★~B₂)
    with consistent-common-lowerᶜ B ★~B₁
       | consistent-common-lowerᶜ B ★~B₂
... | C₁ , C₁⊑★ , C₁⊑B₁ | C₂ , C₂⊑★ , C₂⊑B₂ =
      C₁ ⇒ C₂ , tag_⇒_ C₁⊑★ C₂⊑★ , C₁⊑B₁ ↦ C₂⊑B₂
consistent-common-lowerᶜ B (★-~-νX ★~x)
    with bounds-star-var B ★~x
... | z , z⊑★ , z⊑x = ＇ z , tagˣ z⊑★ , idˣ z⊑x
consistent-common-lowerᶜ B (∀-~-B occA A~B)
    with consistent-common-lowerᶜ (BoundsCtx-∀ν B) A~B
... | C , C⊑A , C⊑B =
      `∀ C , ∀ⁱ C⊑A , ν (plainν-target-occurs-source C⊑A occA) C⊑B
consistent-common-lowerᶜ B (A-~-∀ occB A~B)
    with consistent-common-lowerᶜ (BoundsCtx-ν∀ B) A~B
... | C , C⊑A , C⊑B =
      `∀ C , ν (plainν-target-occurs-source C⊑B occB) C⊑A , ∀ⁱ C⊑B

consistent-common-lower :
  ∀ {A B} →
  [] ⊢ A ~ B →
  CommonLower A B
consistent-common-lower = consistent-common-lowerᶜ BoundsCtx-[]

common-lower-consistent :
  ∀ {A B} →
  CommonLower A B →
  [] ⊢ A ~ B
common-lower-consistent (_ , C⊑A , C⊑B) =
  lower-bounds-consistent C⊑A C⊑B

consistency-iff-common-lower :
  ∀ {A B} →
  ([] ⊢ A ~ B → CommonLower A B) ×
  (CommonLower A B → [] ⊢ A ~ B)
consistency-iff-common-lower =
  consistent-common-lower , common-lower-consistent

glb-exists-consistent :
  ∀ {A B} →
  (Σ[ C ∈ Ty ] 0 ⊢ C ＝ A ⊓ B) →
  [] ⊢ A ~ B
glb-exists-consistent (C , C⊓A⊓B) =
  common-lower-consistent (C , proj₁ C⊓A⊓B , proj₁ (proj₂ C⊓A⊓B))

------------------------------------------------------------------------
-- Core consistency cases as GLB witnesses
------------------------------------------------------------------------

consistent-glb-★-★ᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ} →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C ★ ★
consistent-glb-★-★ᶜ G = ★ , glbᶜ-star-star G

consistent-glb-ι-ιᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C (‵ ι) (‵ ι)
consistent-glb-ι-ιᶜ = ‵ _ , glbᶜ-base-base

consistent-glb-ι-★ᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C (‵ ι) ★
consistent-glb-ι-★ᶜ = ‵ _ , glbᶜ-base-star

consistent-glb-★-ιᶜ :
  ∀ {Φᴸ Φᴿ Φᴼ ι} →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C ★ (‵ ι)
consistent-glb-★-ιᶜ = ‵ _ , glbᶜ-star-base

consistent-glb-X-Yᶜ :
  ∀ {Γ Φᴸ Φᴿ Φᴼ X Y} →
  BoundsCtx Γ Φᴸ Φᴿ →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (X ~ᶜ Y) ∈ Γ →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C (＇ X) (＇ Y)
consistent-glb-X-Yᶜ B G x~y with bounds-var-var B x~y
consistent-glb-X-Yᶜ B G x~y | z , z⊑x , z⊑y
    with glbᶜ-var-var G z⊑x z⊑y
consistent-glb-X-Yᶜ B G x~y | z , z⊑x , z⊑y | z′ , glb =
  ＇ z′ , glb

consistent-glb-X-★ᶜ :
  ∀ {Γ Φᴸ Φᴿ Φᴼ X} →
  BoundsCtx Γ Φᴸ Φᴿ →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (X ~ᶜ★) ∈ Γ →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C (＇ X) ★
consistent-glb-X-★ᶜ B G x~★ with bounds-var-star B x~★
consistent-glb-X-★ᶜ B G x~★ | z , z⊑x , z⊑★
    with glbᶜ-var-star G z⊑x z⊑★
consistent-glb-X-★ᶜ B G x~★ | z , z⊑x , z⊑★ | z′ , glb =
  ＇ z′ , glb

consistent-glb-★-Xᶜ :
  ∀ {Γ Φᴸ Φᴿ Φᴼ X} →
  BoundsCtx Γ Φᴸ Φᴿ →
  GlbCtx Φᴸ Φᴿ Φᴼ →
  (★~ᶜ X) ∈ Γ →
  Σ[ C ∈ Ty ] Glbᶜ Φᴸ Φᴿ Φᴼ C ★ (＇ X)
consistent-glb-★-Xᶜ B G ★~x with bounds-star-var B ★~x
consistent-glb-★-Xᶜ B G ★~x | z , z⊑★ , z⊑x
    with glbᶜ-star-var G z⊑★ z⊑x
consistent-glb-★-Xᶜ B G ★~x | z , z⊑★ , z⊑x | z′ , glb =
  ＇ z′ , glb

consistent-glb-★-★ :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ ★ ⊓ ★
consistent-glb-★-★ =
  ★ , glbᶜ-closed⇒⊓ (glbᶜ-star-star GlbCtx-[])

------------------------------------------------------------------------
-- GLB search, mirroring the shape of consistent?
------------------------------------------------------------------------

record GlbSearch (A B : Ty) : Set where
  constructor glb-search
  field
    Φᴸ : ImpCtx
    Φᴿ : ImpCtx
    Φᴼ : ImpCtx
    meet : Ty
    glb : Glbᶜ Φᴸ Φᴿ Φᴼ meet A B

open GlbSearch public

data GlbSearch⁺ : Ty → Ty → Set where
  glb-left :
    ∀ {Φᴸ Φᴿ A B} →
    Glbᶜ Φᴸ Φᴿ Φᴸ A A B →
    GlbSearch⁺ A B

  glb-right :
    ∀ {Φᴸ Φᴿ A B} →
    Glbᶜ Φᴸ Φᴿ Φᴿ B A B →
    GlbSearch⁺ A B

  glb-any :
    ∀ {Φᴸ Φᴿ Φᴼ A B C} →
    Glbᶜ Φᴸ Φᴿ Φᴼ C A B →
    GlbSearch⁺ A B

  glb-mixed-left-right :
    ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ Φᴸ Φᴿ Φᴼ A₁ A₂ B₁ B₂ C} →
    Glbᶜ Φᴸ₁ Φᴿ₁ Φᴸ₁ A₁ A₁ B₁ →
    Glbᶜ Φᴸ₂ Φᴿ₂ Φᴿ₂ B₂ A₂ B₂ →
    Glbᶜ Φᴸ Φᴿ Φᴼ C (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
    GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂)

  glb-mixed-right-left :
    ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ Φᴸ Φᴿ Φᴼ A₁ A₂ B₁ B₂ C} →
    Glbᶜ Φᴸ₁ Φᴿ₁ Φᴿ₁ B₁ A₁ B₁ →
    Glbᶜ Φᴸ₂ Φᴿ₂ Φᴸ₂ A₂ A₂ B₂ →
    Glbᶜ Φᴸ Φᴿ Φᴼ C (A₁ ⇒ A₂) (B₁ ⇒ B₂) →
    GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂)

to-search : ∀ {A B} → GlbSearch⁺ A B → GlbSearch A B
to-search (glb-left {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} glb) =
  glb-search Φᴸ Φᴿ Φᴸ _ glb
to-search (glb-right {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} glb) =
  glb-search Φᴸ Φᴿ Φᴿ _ glb
to-search (glb-any {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {Φᴼ = Φᴼ} {C = C} glb) =
  glb-search Φᴸ Φᴿ Φᴼ C glb
to-search
    (glb-mixed-left-right {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Φᴼ = Φᴼ} {C = C} _ _ glb) =
  glb-search Φᴸ Φᴿ Φᴼ C glb
to-search
    (glb-mixed-right-left {Φᴸ = Φᴸ} {Φᴿ = Φᴿ}
      {Φᴼ = Φᴼ} {C = C} _ _ glb) =
  glb-search Φᴸ Φᴿ Φᴼ C glb

cast-search⁺ˡ :
  ∀ {A A′ B} →
  A ≡ A′ →
  GlbSearch⁺ A B →
  GlbSearch⁺ A′ B
cast-search⁺ˡ refl result = result

cast-search⁺ʳ :
  ∀ {A B B′} →
  B ≡ B′ →
  GlbSearch⁺ A B →
  GlbSearch⁺ A B′
cast-search⁺ʳ refl result = result

GlbCtx-var-var-single :
  ∀ {X Y} →
  GlbCtx ((X ˣ⊑ˣ X) ∷ []) ((X ˣ⊑ˣ Y) ∷ []) ((X ˣ⊑ˣ X) ∷ [])
GlbCtx-var-var-single {X = X} .glb-var-var (here refl) (here refl) =
  X , here refl , here refl , greatest
  where
  greatest :
    ∀ {W′} →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ [] →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ [] →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ []
  greatest (here refl) (here refl) = here refl
GlbCtx-var-var-single .glb-var-var (here refl) (there ())
GlbCtx-var-var-single .glb-var-var (there ()) _
GlbCtx-var-var-single .glb-var-star _ (here ())
GlbCtx-var-var-single .glb-var-star _ (there ())
GlbCtx-var-var-single .glb-star-var (here ()) _
GlbCtx-var-var-single .glb-star-var (there ()) _
GlbCtx-var-var-single .glb-star-star (here ()) _
GlbCtx-var-var-single .glb-star-star (there ()) _

GlbCtx-var-star-single :
  ∀ {X} →
  GlbCtx ((X ˣ⊑ˣ X) ∷ []) ((X ˣ⊑★) ∷ []) ((X ˣ⊑ˣ X) ∷ [])
GlbCtx-var-star-single .glb-var-var _ (here ())
GlbCtx-var-star-single .glb-var-var _ (there ())
GlbCtx-var-star-single {X = X} .glb-var-star (here refl) (here refl) =
  X , here refl , here refl , greatest
  where
  greatest :
    ∀ {W′} →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ [] →
    (W′ ˣ⊑★) ∈ (_ ˣ⊑★) ∷ [] →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ []
  greatest (here refl) (here refl) = here refl
GlbCtx-var-star-single .glb-var-star (here refl) (there ())
GlbCtx-var-star-single .glb-var-star (there ()) _
GlbCtx-var-star-single .glb-star-var (here ()) _
GlbCtx-var-star-single .glb-star-var (there ()) _
GlbCtx-var-star-single .glb-star-star (here ()) _
GlbCtx-var-star-single .glb-star-star (there ()) _

GlbCtx-star-var-single :
  ∀ {X Y} →
  GlbCtx ((X ˣ⊑★) ∷ []) ((X ˣ⊑ˣ Y) ∷ []) ((X ˣ⊑ˣ X) ∷ [])
GlbCtx-star-var-single .glb-var-var (here ()) _
GlbCtx-star-var-single .glb-var-var (there ()) _
GlbCtx-star-var-single .glb-var-star (here ()) _
GlbCtx-star-var-single .glb-var-star (there ()) _
GlbCtx-star-var-single {X = X} .glb-star-var (here refl) (here refl) =
  X , here refl , here refl , greatest
  where
  greatest :
    ∀ {W′} →
    (W′ ˣ⊑★) ∈ (_ ˣ⊑★) ∷ [] →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ [] →
    (W′ ˣ⊑ˣ _) ∈ (_ ˣ⊑ˣ _) ∷ []
  greatest (here refl) (here refl) = here refl
GlbCtx-star-var-single .glb-star-var (here refl) (there ())
GlbCtx-star-var-single .glb-star-var (there ()) _
GlbCtx-star-var-single .glb-star-star _ (here ())
GlbCtx-star-var-single .glb-star-star _ (there ())

glbᶜ-var-var-single-core :
  ∀ {X Y} →
  Glbᶜ ((X ˣ⊑ˣ X) ∷ []) ((X ˣ⊑ˣ Y) ∷ [])
       ((X ˣ⊑ˣ X) ∷ []) (＇ X) (＇ X) (＇ Y)
glbᶜ-var-var-single-core =
  glbᶜ-intro (idˣ (here refl)) (idˣ (here refl))
    (λ D D⊑X D⊑Y → greatest-var-varᵍ greatest D⊑X D⊑Y)
  where
  greatest :
    ∀ {X Y W} →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ [] →
    (W ˣ⊑ˣ Y) ∈ (X ˣ⊑ˣ Y) ∷ [] →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ []
  greatest (here refl) (here refl) = here refl

glbᶜ-var-star-single-core :
  ∀ {X} →
  Glbᶜ ((X ˣ⊑ˣ X) ∷ []) ((X ˣ⊑★) ∷ [])
       ((X ˣ⊑ˣ X) ∷ []) (＇ X) (＇ X) ★
glbᶜ-var-star-single-core =
  glbᶜ-intro (idˣ (here refl)) (tagˣ (here refl))
    (λ D D⊑X D⊑★ → greatest-var-starᵍ greatest D⊑X D⊑★)
  where
  greatest :
    ∀ {X W} →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ [] →
    (W ˣ⊑★) ∈ (X ˣ⊑★) ∷ [] →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ []
  greatest (here refl) (here refl) = here refl

glbᶜ-star-var-single-core :
  ∀ {X} →
  Glbᶜ ((X ˣ⊑★) ∷ []) ((X ˣ⊑ˣ X) ∷ [])
       ((X ˣ⊑ˣ X) ∷ []) (＇ X) ★ (＇ X)
glbᶜ-star-var-single-core =
  glbᶜ-intro (tagˣ (here refl)) (idˣ (here refl))
    (λ D D⊑★ D⊑X → greatest-star-varᵍ greatest D⊑★ D⊑X)
  where
  greatest :
    ∀ {X W} →
    (W ˣ⊑★) ∈ (X ˣ⊑★) ∷ [] →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ [] →
    (W ˣ⊑ˣ X) ∈ (X ˣ⊑ˣ X) ∷ []
  greatest (here refl) (here refl) = here refl

core-glb-atomic? :
  (A B : Ty) →
  Non∀ A →
  Non∀ B →
  Maybe (GlbSearch⁺ A B)
core-glb-atomic? (＇ X) (＇ Y) nA nB =
  just (glb-left glbᶜ-var-var-single-core)
core-glb-atomic? (＇ X) (｀ α) nA nB = nothing
core-glb-atomic? (＇ X) (‵ ι) nA nB = nothing
core-glb-atomic? (＇ X) ★ nA nB =
  just (glb-left glbᶜ-var-star-single-core)
core-glb-atomic? (＇ X) (B₁ ⇒ B₂) nA nB = nothing
core-glb-atomic? (｀ α) B nA nB = nothing
core-glb-atomic? (‵ ι) (＇ X) nA nB = nothing
core-glb-atomic? (‵ ι) (｀ α) nA nB = nothing
core-glb-atomic? (‵ ι) (‵ ι′) nA nB with ι ≟Base ι′
core-glb-atomic? (‵ ι) (‵ .ι) nA nB | yes refl =
  just (glb-left (glbᶜ-base-base {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}
                                    {ι = ι}))
core-glb-atomic? (‵ ι) (‵ ι′) nA nB | no neq = nothing
core-glb-atomic? (‵ ι) ★ nA nB =
  just (glb-left (glbᶜ-base-star {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}
                                    {ι = ι}))
core-glb-atomic? (‵ ι) (B₁ ⇒ B₂) nA nB = nothing
core-glb-atomic? ★ (＇ X) nA nB =
  just (glb-right glbᶜ-star-var-single-core)
core-glb-atomic? ★ (｀ α) nA nB = nothing
core-glb-atomic? ★ (‵ ι) nA nB =
  just (glb-right (glbᶜ-star-base {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}
                                    {ι = ι}))
core-glb-atomic? ★ ★ nA nB =
  just (glb-left (glbᶜ-star-star GlbCtx-[]))
core-glb-atomic? ★ (B₁ ⇒ B₂) nA nB = nothing
core-glb-atomic? (A₁ ⇒ A₂) B nA nB = nothing

cast-⊓ˡ :
  ∀ {Ψ A B B′ C} →
  B ≡ B′ →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ⊢ A ＝ B′ ⊓ C
cast-⊓ˡ refl glb = glb

cast-⊓ʳ :
  ∀ {Ψ A B C C′} →
  C ≡ C′ →
  Ψ ⊢ A ＝ B ⊓ C →
  Ψ ⊢ A ＝ B ⊓ C′
cast-⊓ʳ refl glb = glb

cast-Glbᶜ :
  ∀ {Φᴸ Φᴸ′ Φᴿ Φᴿ′ Φᴼ Φᴼ′ A B C} →
  Φᴸ ≡ Φᴸ′ →
  Φᴿ ≡ Φᴿ′ →
  Φᴼ ≡ Φᴼ′ →
  Glbᶜ Φᴸ Φᴿ Φᴼ C A B →
  Glbᶜ Φᴸ′ Φᴿ′ Φᴼ′ C A B
cast-Glbᶜ refl refl refl glb = glb

_≟ImpAssm_ : (a b : ImpAssm) → Dec (a ≡ b)
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑★) with x ≟ y
(x ˣ⊑★) ≟ImpAssm (.x ˣ⊑★) | yes refl = yes refl
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑★) | no neq =
  no (λ { refl → neq refl })
(x ˣ⊑★) ≟ImpAssm (y ˣ⊑ˣ z) = no (λ ())
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑★) = no (λ ())
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑ˣ w) with x ≟ z | y ≟ w
(x ˣ⊑ˣ y) ≟ImpAssm (.x ˣ⊑ˣ .y) | yes refl | yes refl =
  yes refl
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑ˣ w) | no neq | _ =
  no (λ { refl → neq refl })
(x ˣ⊑ˣ y) ≟ImpAssm (z ˣ⊑ˣ w) | _ | no neq =
  no (λ { refl → neq refl })

_≟ImpCtx_ : (Φ Ψ : ImpCtx) → Dec (Φ ≡ Ψ)
[] ≟ImpCtx [] = yes refl
[] ≟ImpCtx (_ ∷ _) = no (λ ())
(_ ∷ _) ≟ImpCtx [] = no (λ ())
(a ∷ Φ) ≟ImpCtx (b ∷ Ψ) with a ≟ImpAssm b | Φ ≟ImpCtx Ψ
(a ∷ Φ) ≟ImpCtx (.a ∷ .Φ) | yes refl | yes refl = yes refl
(a ∷ Φ) ≟ImpCtx (b ∷ Ψ) | no neq | _ =
  no (λ { refl → neq refl })
(a ∷ Φ) ≟ImpCtx (b ∷ Ψ) | _ | no neq =
  no (λ { refl → neq refl })

closed-search⇒⊓ :
  ∀ {A B} →
  GlbSearch A B →
  Maybe (Σ[ C ∈ Ty ] 0 ⊢ C ＝ A ⊓ B)
closed-search⇒⊓ (glb-search [] [] [] C glb) =
  just (C , glbᶜ-closed⇒⊓ glb)
closed-search⇒⊓ _ = nothing

ImpCtxMap : ImpCtx → ImpCtx → Set
ImpCtxMap Φ Ψ = ∀ {a} → a ∈ Φ → a ∈ Ψ

⇑ᵢₐ-∈ : ∀ {a Φ} → a ∈ Φ → ⇑ᵢₐ a ∈ ⇑ᵢ Φ
⇑ᵢₐ-∈ {a = _ ˣ⊑★} a∈Φ = ⇑ᵢ-★∈ a∈Φ
⇑ᵢₐ-∈ {a = _ ˣ⊑ˣ _} a∈Φ = ⇑ᵢ-ˣ∈ a∈Φ

⇑ᴸᵢₐ-∈ : ∀ {a Φ} → a ∈ Φ → ⇑ᴸᵢₐ a ∈ ⇑ᴸᵢ Φ
⇑ᴸᵢₐ-∈ {a = _ ˣ⊑★} a∈Φ = ⇑ᴸᵢ-★∈ a∈Φ
⇑ᴸᵢₐ-∈ {a = _ ˣ⊑ˣ _} a∈Φ = ⇑ᴸᵢ-ˣ∈ a∈Φ

map⇑ᵢ∈ :
  ∀ {Φ Ψ} →
  ImpCtxMap Φ Ψ →
  ImpCtxMap (⇑ᵢ Φ) (⇑ᵢ Ψ)
map⇑ᵢ∈ {Φ = []} f ()
map⇑ᵢ∈ {Φ = a ∷ Φ} f (here refl) = ⇑ᵢₐ-∈ (f (here refl))
map⇑ᵢ∈ {Φ = a ∷ Φ} f (there a∈⇑Φ) =
  map⇑ᵢ∈ (λ z∈Φ → f (there z∈Φ)) a∈⇑Φ

map⇑ᴸᵢ∈ :
  ∀ {Φ Ψ} →
  ImpCtxMap Φ Ψ →
  ImpCtxMap (⇑ᴸᵢ Φ) (⇑ᴸᵢ Ψ)
map⇑ᴸᵢ∈ {Φ = []} f ()
map⇑ᴸᵢ∈ {Φ = a ∷ Φ} f (here refl) = ⇑ᴸᵢₐ-∈ (f (here refl))
map⇑ᴸᵢ∈ {Φ = a ∷ Φ} f (there a∈⇑Φ) =
  map⇑ᴸᵢ∈ (λ z∈Φ → f (there z∈Φ)) a∈⇑Φ

map-∀ᵢ : ∀ {Φ Ψ} → ImpCtxMap Φ Ψ →
  ImpCtxMap ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ) ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Ψ)
map-∀ᵢ f (here refl) = here refl
map-∀ᵢ f (there a∈⇑Φ) = there (map⇑ᵢ∈ f a∈⇑Φ)

map-νᵢ : ∀ {Φ Ψ} → ImpCtxMap Φ Ψ →
  ImpCtxMap ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
map-νᵢ f (here refl) = here refl
map-νᵢ f (there a∈⇑Φ) = there (map⇑ᴸᵢ∈ f a∈⇑Φ)

map-⊑ :
  ∀ {Ψ Φ Φ′ A B} →
  ImpCtxMap Φ Φ′ →
  Ψ ∣ Φ ⊢ A ⊑ B →
  Ψ ∣ Φ′ ⊢ A ⊑ B
map-⊑ f id★ = id★
map-⊑ f (idˣ x⊑y) = idˣ (f x⊑y)
map-⊑ f idι = idι
map-⊑ f (idα (wfSeal α<Ψ)) = idα (wfSeal α<Ψ)
map-⊑ f (p ↦ q) = map-⊑ f p ↦ map-⊑ f q
map-⊑ f (∀ⁱ p) = ∀ⁱ map-⊑ (map-∀ᵢ f) p
map-⊑ f (tag ι) = tag ι
map-⊑ f (tag_⇒_ p q) = tag_⇒_ (map-⊑ f p) (map-⊑ f q)
map-⊑ f (tagˣ x⊑★) = tagˣ (f x⊑★)
map-⊑ f (ν occA p) = ν occA (map-⊑ (map-νᵢ f) p)

weaken-⊑-∷ :
  ∀ {Ψ a Φ A B} →
  Ψ ∣ Φ ⊢ A ⊑ B →
  Ψ ∣ a ∷ Φ ⊢ A ⊑ B
weaken-⊑-∷ = map-⊑ there

weaken-⊑-++ˡ :
  ∀ {Ψ Φ Φ′ A B} →
  Ψ ∣ Φ ⊢ A ⊑ B →
  Ψ ∣ Φ ++ Φ′ ⊢ A ⊑ B
weaken-⊑-++ˡ = map-⊑ ∈-++ˡ

weaken-⊑-++ʳ :
  ∀ {Ψ Φ′ A B} →
  (Φ : ImpCtx) →
  Ψ ∣ Φ′ ⊢ A ⊑ B →
  Ψ ∣ Φ ++ Φ′ ⊢ A ⊑ B
weaken-⊑-++ʳ Φ = map-⊑ (∈-++ʳ Φ)

head-++ˡ :
  ∀ {a Φ Φ′} →
  ImpCtxMap (a ∷ Φ) (a ∷ (Φ ++ Φ′))
head-++ˡ (here refl) = here refl
head-++ˡ (there a∈Φ) = there (∈-++ˡ a∈Φ)

head-++ʳ :
  ∀ {a Φ Φ′} →
  ImpCtxMap (a ∷ Φ′) (a ∷ (Φ ++ Φ′))
head-++ʳ (here refl) = here refl
head-++ʳ (there a∈Φ′) = there (∈-++ʳ _ a∈Φ′)

weaken-⊑-head-++ˡ :
  ∀ {Ψ a Φ Φ′ A B} →
  Ψ ∣ a ∷ Φ ⊢ A ⊑ B →
  Ψ ∣ a ∷ (Φ ++ Φ′) ⊢ A ⊑ B
weaken-⊑-head-++ˡ = map-⊑ head-++ˡ

weaken-⊑-head-++ʳ :
  ∀ {Ψ a Φ Φ′ A B} →
  Ψ ∣ a ∷ Φ′ ⊢ A ⊑ B →
  Ψ ∣ a ∷ (Φ ++ Φ′) ⊢ A ⊑ B
weaken-⊑-head-++ʳ = map-⊑ head-++ʳ

glbᶜ-left-cons :
  ∀ {aᴸ aᴿ Φᴸ Φᴿ A B} →
  Glbᶜ Φᴸ Φᴿ Φᴸ A A B →
  Glbᶜ (aᴸ ∷ Φᴸ) (aᴿ ∷ Φᴿ) (aᴸ ∷ Φᴸ) A A B
glbᶜ-left-cons glb =
  glbᶜ-intro
    (weaken-⊑-∷ (lowerˡᶜ glb))
    (weaken-⊑-∷ (lowerʳᶜ glb))
    (λ D D⊑A _ → D⊑A)

glbᶜ-right-cons :
  ∀ {aᴸ aᴿ Φᴸ Φᴿ A B} →
  Glbᶜ Φᴸ Φᴿ Φᴿ B A B →
  Glbᶜ (aᴸ ∷ Φᴸ) (aᴿ ∷ Φᴿ) (aᴿ ∷ Φᴿ) B A B
glbᶜ-right-cons glb =
  glbᶜ-intro
    (weaken-⊑-∷ (lowerˡᶜ glb))
    (weaken-⊑-∷ (lowerʳᶜ glb))
    (λ D _ D⊑B → D⊑B)

glbᶜ-left-map :
  ∀ {Φᴸ Φᴿ Φᴸ′ Φᴿ′ A B} →
  ImpCtxMap Φᴸ Φᴸ′ →
  ImpCtxMap Φᴿ Φᴿ′ →
  Glbᶜ Φᴸ Φᴿ Φᴸ A A B →
  Glbᶜ Φᴸ′ Φᴿ′ Φᴸ′ A A B
glbᶜ-left-map f g glb =
  glbᶜ-intro
    (map-⊑ f (lowerˡᶜ glb))
    (map-⊑ g (lowerʳᶜ glb))
    (λ D D⊑A _ → D⊑A)

glbᶜ-right-map :
  ∀ {Φᴸ Φᴿ Φᴸ′ Φᴿ′ A B} →
  ImpCtxMap Φᴸ Φᴸ′ →
  ImpCtxMap Φᴿ Φᴿ′ →
  Glbᶜ Φᴸ Φᴿ Φᴿ B A B →
  Glbᶜ Φᴸ′ Φᴿ′ Φᴿ′ B A B
glbᶜ-right-map f g glb =
  glbᶜ-intro
    (map-⊑ f (lowerˡᶜ glb))
    (map-⊑ g (lowerʳᶜ glb))
    (λ D _ D⊑B → D⊑B)

ImpVarCtxMap : ImpCtx → ImpCtx → Set
ImpVarCtxMap Φ Ψ = ∀ {X Y} → (X ˣ⊑ˣ Y) ∈ Φ → (X ˣ⊑ˣ Y) ∈ Ψ

map⇑ᵢ-var∈ :
  ∀ {Φ Ψ} →
  ImpVarCtxMap Φ Ψ →
  ImpVarCtxMap (⇑ᵢ Φ) (⇑ᵢ Ψ)
map⇑ᵢ-var∈ {Φ = []} f ()
map⇑ᵢ-var∈ {Φ = (X ˣ⊑★) ∷ Φ} f (here ())
map⇑ᵢ-var∈ {Φ = (X ˣ⊑★) ∷ Φ} f (there x⊑y) =
  map⇑ᵢ-var∈ (λ z∈Φ → f (there z∈Φ)) x⊑y
map⇑ᵢ-var∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (here refl) =
  ⇑ᵢ-ˣ∈ (f (here refl))
map⇑ᵢ-var∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (there x⊑y) =
  map⇑ᵢ-var∈ (λ z∈Φ → f (there z∈Φ)) x⊑y

map⇑ᴸᵢ-var∈ :
  ∀ {Φ Ψ} →
  ImpVarCtxMap Φ Ψ →
  ImpVarCtxMap (⇑ᴸᵢ Φ) (⇑ᴸᵢ Ψ)
map⇑ᴸᵢ-var∈ {Φ = []} f ()
map⇑ᴸᵢ-var∈ {Φ = (X ˣ⊑★) ∷ Φ} f (here ())
map⇑ᴸᵢ-var∈ {Φ = (X ˣ⊑★) ∷ Φ} f (there x⊑y) =
  map⇑ᴸᵢ-var∈ (λ z∈Φ → f (there z∈Φ)) x⊑y
map⇑ᴸᵢ-var∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (here refl) =
  ⇑ᴸᵢ-ˣ∈ (f (here refl))
map⇑ᴸᵢ-var∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (there x⊑y) =
  map⇑ᴸᵢ-var∈ (λ z∈Φ → f (there z∈Φ)) x⊑y

map-ν-var∈ :
  ∀ {Φ Ψ} →
  ImpVarCtxMap Φ Ψ →
  ImpVarCtxMap ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
map-ν-var∈ f (here ())
map-ν-var∈ f (there x⊑y) = there (map⇑ᴸᵢ-var∈ f x⊑y)

map-var-target-⊑ :
  ∀ {Ψ Φ Φ′ A X} →
  ImpVarCtxMap Φ Φ′ →
  Ψ ∣ Φ ⊢ A ⊑ ＇ X →
  Ψ ∣ Φ′ ⊢ A ⊑ ＇ X
map-var-target-⊑ f (idˣ x⊑y) = idˣ (f x⊑y)
map-var-target-⊑ f (ν occA p) =
  ν occA (map-var-target-⊑ (map-ν-var∈ f) p)

ImpVarTargetMap : ImpCtx → ImpCtx → TyVar → TyVar → Set
ImpVarTargetMap Φ Ψ y z = ∀ {x} → (x ˣ⊑ˣ y) ∈ Φ → (x ˣ⊑ˣ z) ∈ Ψ

map⇑ᴸᵢ-target∈ :
  ∀ {Φ Ψ Y Z} →
  ImpVarTargetMap Φ Ψ Y Z →
  ImpVarTargetMap (⇑ᴸᵢ Φ) (⇑ᴸᵢ Ψ) Y Z
map⇑ᴸᵢ-target∈ {Φ = []} f ()
map⇑ᴸᵢ-target∈ {Φ = (X ˣ⊑★) ∷ Φ} f (there x⊑y) =
  map⇑ᴸᵢ-target∈ (λ z∈Φ → f (there z∈Φ)) x⊑y
map⇑ᴸᵢ-target∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (here refl) =
  ⇑ᴸᵢ-ˣ∈ (f (here refl))
map⇑ᴸᵢ-target∈ {Φ = (X ˣ⊑ˣ Y) ∷ Φ} f (there x⊑y) =
  map⇑ᴸᵢ-target∈ (λ z∈Φ → f (there z∈Φ)) x⊑y

map-ν-target∈ :
  ∀ {Φ Ψ Y Z} →
  ImpVarTargetMap Φ Ψ Y Z →
  ImpVarTargetMap ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Ψ) Y Z
map-ν-target∈ f (here ())
map-ν-target∈ f (there x⊑y) = there (map⇑ᴸᵢ-target∈ f x⊑y)

map-var-target-change-⊑ :
  ∀ {Ψ Φ Φ′ A Y Z} →
  ImpVarTargetMap Φ Φ′ Y Z →
  Ψ ∣ Φ ⊢ A ⊑ ＇ Y →
  Ψ ∣ Φ′ ⊢ A ⊑ ＇ Z
map-var-target-change-⊑ f (idˣ x⊑y) = idˣ (f x⊑y)
map-var-target-change-⊑ f (ν occA p) =
  ν occA (map-var-target-change-⊑ (map-ν-target∈ f) p)

data Arrow∀Lower² (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Ty → Ty → Set where
  via-arrow∀ :
    ∀ {A₁ A₂ B₁ B₂ C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ A₁ ⇒ A₂ →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ C ⊑ B₁ ⇒ B₂ →
    Arrow∀Lower² Φᴸ Φᴿ (`∀ C) A₁ A₂ B₁ B₂

  via-arrowν :
    ∀ {A₁ A₂ B₁ B₂ C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ A₁ ⇒ A₂ →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ `∀ (B₁ ⇒ B₂) →
    Arrow∀Lower² Φᴸ Φᴿ (`∀ C) A₁ A₂ B₁ B₂

arrow∀-lower²-inv :
  ∀ {Φᴸ Φᴿ A₁ A₂ B₁ B₂ D} →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ `∀ (B₁ ⇒ B₂) →
  Arrow∀Lower² Φᴸ Φᴿ D A₁ A₂ B₁ B₂
arrow∀-lower²-inv (ν occC p) (∀ⁱ q) = via-arrow∀ occC p q
arrow∀-lower²-inv (ν occC p) (ν _ q) = via-arrowν occC p q

data ∀ArrowLower² (Φᴸ Φᴿ : ImpCtx) : Ty → Ty → Ty → Ty → Ty → Set where
  via-∀arrow :
    ∀ {A₁ A₂ B₁ B₂ C} →
    0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ C ⊑ A₁ ⇒ A₂ →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ B₁ ⇒ B₂ →
    ∀ArrowLower² Φᴸ Φᴿ (`∀ C) A₁ A₂ B₁ B₂

  via-νarrow :
    ∀ {A₁ A₂ B₁ B₂ C} →
    occurs zero C ≡ true →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ C ⊑ `∀ (A₁ ⇒ A₂) →
    0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ C ⊑ B₁ ⇒ B₂ →
    ∀ArrowLower² Φᴸ Φᴿ (`∀ C) A₁ A₂ B₁ B₂

∀arrow-lower²-inv :
  ∀ {Φᴸ Φᴿ A₁ A₂ B₁ B₂ D} →
  0 ∣ Φᴸ ⊢ D ⊑ `∀ (A₁ ⇒ A₂) →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ B₂ →
  ∀ArrowLower² Φᴸ Φᴿ D A₁ A₂ B₁ B₂
∀arrow-lower²-inv (∀ⁱ p) (ν occC q) = via-∀arrow p occC q
∀arrow-lower²-inv (ν occC p) (ν _ q) = via-νarrow occC p q

lower-base-context-free :
  ∀ {Ψ Φ Φ′ D ι} →
  Ψ ∣ Φ ⊢ D ⊑ ‵ ι →
  Ψ ∣ Φ′ ⊢ D ⊑ ‵ ι
lower-base-context-free idι = idι
lower-base-context-free (ν occD p) =
  ν occD (lower-base-context-free p)

greatest-arrow-left-right-base-base :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D ι κ} →
  0 ∣ Φᴸ ⊢ D ⊑ ‵ ι ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ‵ κ →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ ι ⇒ ‵ κ
greatest-arrow-left-right-base-base (D⊑ι ↦ _) (_ ↦ D⊑κ) =
  lower-base-context-free D⊑ι ↦ lower-base-context-free D⊑κ
greatest-arrow-left-right-base-base (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-left-right-base-base D⊑A D⊑B)

glbᶜ-arrow-left-right-base-base :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ ι κ} →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι) (‵ ι) B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ κ) A₂ (‵ κ) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι ⇒ ‵ κ) (‵ ι ⇒ A₂) (B₁ ⇒ ‵ κ)
glbᶜ-arrow-left-right-base-base glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-base-base D⊑A D⊑B)

greatest-arrow-right-left-base-base :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D ι κ} →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ‵ κ →
  0 ∣ Φᴿ ⊢ D ⊑ ‵ ι ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ ι ⇒ ‵ κ
greatest-arrow-right-left-base-base (_ ↦ D⊑κ) (D⊑ι ↦ _) =
  lower-base-context-free D⊑ι ↦ lower-base-context-free D⊑κ
greatest-arrow-right-left-base-base (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-right-left-base-base D⊑A D⊑B)

glbᶜ-arrow-right-left-base-base :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ ι κ} →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι) A₁ (‵ ι) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ κ) (‵ κ) B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ ι ⇒ ‵ κ) (A₁ ⇒ ‵ κ) (‵ ι ⇒ B₂)
glbᶜ-arrow-right-left-base-base glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-base-base D⊑A D⊑B)

greatest-arrow-left-right-var-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D X Y} →
  ImpVarCtxMap Φᴸ Φᴼ →
  ImpVarCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ ＇ X ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ＇ Y →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X ⇒ ＇ Y
greatest-arrow-left-right-var-var-map f g (D⊑X ↦ _) (_ ↦ D⊑Y) =
  map-var-target-⊑ f D⊑X ↦ map-var-target-⊑ g D⊑Y
greatest-arrow-left-right-var-var-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-left-right-var-var-map
      (map-ν-var∈ f) (map-ν-var∈ g) D⊑A D⊑B)

greatest-arrow-right-left-var-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D X Y} →
  ImpVarCtxMap Φᴸ Φᴼ →
  ImpVarCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ＇ Y →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ X ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X ⇒ ＇ Y
greatest-arrow-right-left-var-var-map f g (_ ↦ D⊑Y) (D⊑X ↦ _) =
  map-var-target-⊑ g D⊑X ↦ map-var-target-⊑ f D⊑Y
greatest-arrow-right-left-var-var-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-right-left-var-var-map
      (map-ν-var∈ f) (map-ν-var∈ g) D⊑A D⊑B)

greatest-arrow-left-right-target-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D X X′ Y Y′} →
  ImpVarTargetMap Φᴸ Φᴼ X X′ →
  ImpVarTargetMap Φᴿ Φᴼ Y Y′ →
  0 ∣ Φᴸ ⊢ D ⊑ ＇ X ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ＇ Y →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X′ ⇒ ＇ Y′
greatest-arrow-left-right-target-map f g (D⊑X ↦ _) (_ ↦ D⊑Y) =
  map-var-target-change-⊑ f D⊑X ↦
  map-var-target-change-⊑ g D⊑Y
greatest-arrow-left-right-target-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-left-right-target-map
      (map-ν-target∈ f) (map-ν-target∈ g) D⊑A D⊑B)

greatest-arrow-right-left-target-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D X X′ Y Y′} →
  ImpVarTargetMap Φᴸ Φᴼ Y Y′ →
  ImpVarTargetMap Φᴿ Φᴼ X X′ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ＇ Y →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ X ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X′ ⇒ ＇ Y′
greatest-arrow-right-left-target-map f g (_ ↦ D⊑Y) (D⊑X ↦ _) =
  map-var-target-change-⊑ g D⊑X ↦
  map-var-target-change-⊑ f D⊑Y
greatest-arrow-right-left-target-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-right-left-target-map
      (map-ν-target∈ f) (map-ν-target∈ g) D⊑A D⊑B)

greatest-arrow-left-right-var-base-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D X κ} →
  ImpVarCtxMap Φᴸ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ ＇ X ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ‵ κ →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X ⇒ ‵ κ
greatest-arrow-left-right-var-base-map f (D⊑X ↦ _) (_ ↦ D⊑κ) =
  map-var-target-⊑ f D⊑X ↦ lower-base-context-free D⊑κ
greatest-arrow-left-right-var-base-map f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-left-right-var-base-map (map-ν-var∈ f) D⊑A D⊑B)

greatest-arrow-right-left-base-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D X κ} →
  ImpVarCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ‵ κ →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ X ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ ＇ X ⇒ ‵ κ
greatest-arrow-right-left-base-var-map f (_ ↦ D⊑κ) (D⊑X ↦ _) =
  map-var-target-⊑ f D⊑X ↦ lower-base-context-free D⊑κ
greatest-arrow-right-left-base-var-map f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-right-left-base-var-map (map-ν-var∈ f) D⊑A D⊑B)

greatest-arrow-right-left-base-var-from-left :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D Y κ} →
  ImpVarCtxMap Φᴸ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ＇ Y →
  0 ∣ Φᴿ ⊢ D ⊑ ‵ κ ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ κ ⇒ ＇ Y
greatest-arrow-right-left-base-var-from-left f (_ ↦ D⊑Y) (D⊑κ ↦ _) =
  lower-base-context-free D⊑κ ↦ map-var-target-⊑ f D⊑Y
greatest-arrow-right-left-base-var-from-left f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-right-left-base-var-from-left (map-ν-var∈ f) D⊑A D⊑B)

greatest-arrow-left-right-base-var-from-right :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D Y κ} →
  ImpVarCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ ‵ κ ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ＇ Y →
  0 ∣ Φᴼ ⊢ D ⊑ ‵ κ ⇒ ＇ Y
greatest-arrow-left-right-base-var-from-right f (D⊑κ ↦ _) (_ ↦ D⊑Y) =
  lower-base-context-free D⊑κ ↦ map-var-target-⊑ f D⊑Y
greatest-arrow-left-right-base-var-from-right f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-arrow-left-right-base-var-from-right (map-ν-var∈ f) D⊑A D⊑B)

greatest-∀ν-arrow-var-base :
  ∀ {Φ D κ} →
  0 ∣ Φ ⊢ D ⊑ `∀ (＇ 0 ⇒ ★) →
  0 ∣ Φ ⊢ D ⊑ ★ ⇒ ‵ κ →
  0 ∣ Φ ⊢ D ⊑ `∀ (＇ 0 ⇒ ‵ κ)
greatest-∀ν-arrow-var-base (∀ⁱ D⊑A) (ν occD D⊑B) =
  ∀ⁱ (greatest-arrow-left-right-var-base-map (λ x → x) D⊑A D⊑B)
greatest-∀ν-arrow-var-base (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-∀ν-arrow-var-base D⊑A D⊑B)

greatest-ν∀-arrow-base-var :
  ∀ {Φ D κ} →
  0 ∣ Φ ⊢ D ⊑ ★ ⇒ ‵ κ →
  0 ∣ Φ ⊢ D ⊑ `∀ (＇ 0 ⇒ ★) →
  0 ∣ Φ ⊢ D ⊑ `∀ (＇ 0 ⇒ ‵ κ)
greatest-ν∀-arrow-base-var (ν occD D⊑A) (∀ⁱ D⊑B) =
  ∀ⁱ (greatest-arrow-right-left-base-var-map (λ x → x) D⊑A D⊑B)
greatest-ν∀-arrow-base-var (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-ν∀-arrow-base-var D⊑A D⊑B)

greatest-∀ν-arrow-var-codomain :
  ∀ {Φ D κ} →
  0 ∣ Φ ⊢ D ⊑ `∀ (★ ⇒ ＇ 0) →
  0 ∣ Φ ⊢ D ⊑ ‵ κ ⇒ ★ →
  0 ∣ Φ ⊢ D ⊑ `∀ (‵ κ ⇒ ＇ 0)
greatest-∀ν-arrow-var-codomain (∀ⁱ D⊑A) (ν occD D⊑B) =
  ∀ⁱ (greatest-arrow-right-left-base-var-from-left (λ x → x) D⊑A D⊑B)
greatest-∀ν-arrow-var-codomain (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-∀ν-arrow-var-codomain D⊑A D⊑B)

greatest-ν∀-arrow-var-codomain :
  ∀ {Φ D κ} →
  0 ∣ Φ ⊢ D ⊑ ‵ κ ⇒ ★ →
  0 ∣ Φ ⊢ D ⊑ `∀ (★ ⇒ ＇ 0) →
  0 ∣ Φ ⊢ D ⊑ `∀ (‵ κ ⇒ ＇ 0)
greatest-ν∀-arrow-var-codomain (ν occD D⊑A) (∀ⁱ D⊑B) =
  ∀ⁱ (greatest-arrow-left-right-base-var-from-right (λ x → x) D⊑A D⊑B)
greatest-ν∀-arrow-var-codomain (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-ν∀-arrow-var-codomain D⊑A D⊑B)

glbᶜ-arrow-left-right-var-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₂ B₁ X Y} →
  ImpVarCtxMap Φᴸ Φᴼ →
  ImpVarCtxMap Φᴿ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (＇ X) (＇ X) B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (＇ Y) A₂ (＇ Y) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (＇ X ⇒ ＇ Y) (＇ X ⇒ A₂) (B₁ ⇒ ＇ Y)
glbᶜ-arrow-left-right-var-var-map f g glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-var-var-map f g D⊑A D⊑B)

glbᶜ-arrow-left-right-var-base-map :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₂ B₁ X κ} →
  ImpVarCtxMap Φᴸ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (＇ X) (＇ X) B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (‵ κ) A₂ (‵ κ) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (＇ X ⇒ ‵ κ) (＇ X ⇒ A₂) (B₁ ⇒ ‵ κ)
glbᶜ-arrow-left-right-var-base-map f glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-var-base-map f D⊑A D⊑B)

glbᶜ-arrow-right-left-base-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₁ B₂ X κ} →
  ImpVarCtxMap Φᴿ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (＇ X) A₁ (＇ X) →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (‵ κ) (‵ κ) B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴼ (＇ X ⇒ ‵ κ) (A₁ ⇒ ‵ κ) (＇ X ⇒ B₂)
glbᶜ-arrow-right-left-base-var-map f glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-base-var-map f D⊑A D⊑B)

glbᶜ-arrow-right-left-base-var-from-left :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₁ B₂ Y κ} →
  ImpVarCtxMap Φᴸ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (‵ κ) A₁ (‵ κ) →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (＇ Y) (＇ Y) B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ κ ⇒ ＇ Y) (A₁ ⇒ ＇ Y) (‵ κ ⇒ B₂)
glbᶜ-arrow-right-left-base-var-from-left f glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-base-var-from-left f D⊑A D⊑B)

glbᶜ-arrow-left-right-base-var-from-right :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₂ B₁ Y κ} →
  ImpVarCtxMap Φᴿ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (‵ κ) (‵ κ) B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (＇ Y) A₂ (＇ Y) →
  Glbᶜ Φᴸ Φᴿ Φᴼ (‵ κ ⇒ ＇ Y) (‵ κ ⇒ A₂) (B₁ ⇒ ＇ Y)
glbᶜ-arrow-left-right-base-var-from-right f glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-base-var-from-right f D⊑A D⊑B)

glbᶜ-arrow-right-left-var-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ Φᴼ₁ Φᴼ₂ A₁ B₂ X Y} →
  ImpVarCtxMap Φᴸ Φᴼ →
  ImpVarCtxMap Φᴿ Φᴼ →
  Glbᶜ Φᴸ Φᴿ Φᴼ₁ (＇ X) A₁ (＇ X) →
  Glbᶜ Φᴸ Φᴿ Φᴼ₂ (＇ Y) (＇ Y) B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴼ (＇ X ⇒ ＇ Y) (A₁ ⇒ ＇ Y) (＇ X ⇒ B₂)
glbᶜ-arrow-right-left-var-var-map f g glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-var-var-map f g D⊑A D⊑B)

var-star-left-map :
  ImpCtxMap ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ (0 ˣ⊑★) ∷ [])
var-star-left-map (here refl) = here refl
var-star-left-map (there ())

var-star-right-map :
  ImpCtxMap ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑★) ∷ (0 ˣ⊑ˣ 0) ∷ [])
var-star-right-map (here refl) = here refl
var-star-right-map (there ())

star-var-left-map :
  ImpCtxMap ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ (0 ˣ⊑★) ∷ [])
star-var-left-map (here refl) = there (here refl)
star-var-left-map (there ())

star-var-right-map :
  ImpCtxMap ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑★) ∷ (0 ˣ⊑ˣ 0) ∷ [])
star-var-right-map (here refl) = there (here refl)
star-var-right-map (there ())

var-star-var-target-map :
  ImpVarCtxMap ((0 ˣ⊑ˣ 0) ∷ (0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
var-star-var-target-map (here refl) = here refl
var-star-var-target-map (there (here ()))
var-star-var-target-map (there (there ()))

star-var-var-target-map :
  ImpVarCtxMap ((0 ˣ⊑★) ∷ (0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
star-var-var-target-map (here ())
star-var-var-target-map (there (here refl)) = here refl
star-var-var-target-map (there (there ()))

glbᶜ-arrow-var-star-star-var :
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ (0 ˣ⊑★) ∷ [])
       ((0 ˣ⊑★) ∷ (0 ˣ⊑ˣ 0) ∷ [])
       ((0 ˣ⊑ˣ 0) ∷ [])
       (＇ 0 ⇒ ＇ 0) (＇ 0 ⇒ ★) (★ ⇒ ＇ 0)
glbᶜ-arrow-var-star-star-var =
  glbᶜ-arrow-left-right-var-var-map
    var-star-var-target-map
    star-var-var-target-map
    (glbᶜ-left-map
      var-star-left-map var-star-right-map glbᶜ-var-star-single-core)
    (glbᶜ-right-map
      star-var-left-map star-var-right-map glbᶜ-star-var-single-core)

glbᶜ-arrow-star-var-var-star :
  Glbᶜ ((0 ˣ⊑★) ∷ (0 ˣ⊑ˣ 0) ∷ [])
       ((0 ˣ⊑ˣ 0) ∷ (0 ˣ⊑★) ∷ [])
       ((0 ˣ⊑ˣ 0) ∷ [])
       (＇ 0 ⇒ ＇ 0) (★ ⇒ ＇ 0) (＇ 0 ⇒ ★)
glbᶜ-arrow-star-var-var-star =
  glbᶜ-arrow-right-left-var-var-map
    star-var-var-target-map
    var-star-var-target-map
    (glbᶜ-right-map
      var-star-right-map var-star-left-map glbᶜ-star-var-single-core)
    (glbᶜ-left-map
      star-var-right-map star-var-left-map glbᶜ-var-star-single-core)

nested-domain-target-map :
  ImpVarTargetMap
    ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑★) ∷ [])
    ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑ˣ 1) ∷ [])
    0 0
nested-domain-target-map (here refl) = here refl
nested-domain-target-map (there (here ()))
nested-domain-target-map (there (there ()))

nested-codomain-target-map :
  ImpVarTargetMap
    ((0 ˣ⊑★) ∷ (1 ˣ⊑ˣ 0) ∷ [])
    ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑ˣ 1) ∷ [])
    0 1
nested-codomain-target-map (here ())
nested-codomain-target-map (there (here refl)) = there (here refl)
nested-codomain-target-map (there (there ()))

glbᶜ-arrow-var-star-star-var-nested :
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑★) ∷ [])
       ((0 ˣ⊑★) ∷ (1 ˣ⊑ˣ 0) ∷ [])
       ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑ˣ 1) ∷ [])
       (＇ 0 ⇒ ＇ 1) (＇ 0 ⇒ ★) (★ ⇒ ＇ 0)
glbᶜ-arrow-var-star-star-var-nested =
  glbᶜ-intro
    ((idˣ (here refl)) ↦ (tagˣ (there (here refl))))
    ((tagˣ (here refl)) ↦ (idˣ (there (here refl))))
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-target-map
        nested-domain-target-map
        nested-codomain-target-map
        D⊑A D⊑B)

glbᶜ-arrow-star-var-var-star-nested :
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑★) ∷ [])
       ((0 ˣ⊑★) ∷ (1 ˣ⊑ˣ 0) ∷ [])
       ((0 ˣ⊑ˣ 0) ∷ (1 ˣ⊑ˣ 1) ∷ [])
       (＇ 1 ⇒ ＇ 0) (★ ⇒ ＇ 0) (＇ 0 ⇒ ★)
glbᶜ-arrow-star-var-var-star-nested =
  glbᶜ-intro
    ((tagˣ (there (here refl))) ↦ (idˣ (here refl)))
    ((idˣ (there (here refl))) ↦ (tagˣ (here refl)))
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-target-map
        nested-domain-target-map
        nested-codomain-target-map
        D⊑A D⊑B)

plain-zero-target-map :
  ∀ {Φ Φ′} →
  ImpVarTargetMap ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ)
                  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ′)
                  0 0
plain-zero-target-map (here refl) = here refl
plain-zero-target-map (there x⊑0) =
  ⊥-elim (no-⇑ᵢ-zero-right x⊑0)

right-zero-to-one-target-map :
  ∀ {Φ Φ′} →
  ImpVarTargetMap Φ Φ′ 0 0 →
  ImpVarTargetMap ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
                  ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φ′)
                  0 1
right-zero-to-one-target-map f (here ())
right-zero-to-one-target-map f {x = zero} (there x⊑0) =
  ⊥-elim (no-⇑ᴸᵢ-zero-left x⊑0)
right-zero-to-one-target-map f {x = suc x} (there x⊑0) =
  there (⇑ᵢ-ˣ∈ (f (un⇑ᴸᵢ-ˣ∈ x⊑0)))

zero-target-single-map :
  ImpVarTargetMap ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ []) 0 0
zero-target-single-map (here refl) = here refl
zero-target-single-map (there ())

greatest-∀ν-arrow-var-star-star-var-map :
  ∀ {Φᴸ Φᴿ Φᴼ D} →
  ImpVarTargetMap Φᴿ Φᴼ 0 0 →
  0 ∣ Φᴸ ⊢ D ⊑ `∀ (＇ 0 ⇒ ★) →
  0 ∣ Φᴿ ⊢ D ⊑ ★ ⇒ ＇ 0 →
  0 ∣ Φᴼ ⊢ D ⊑ `∀ (＇ 0 ⇒ ＇ 1)
greatest-∀ν-arrow-var-star-star-var-map f (∀ⁱ D⊑A) (ν occD D⊑B) =
  ∀ⁱ
    (greatest-arrow-left-right-target-map
      plain-zero-target-map
      (right-zero-to-one-target-map f)
      D⊑A D⊑B)
greatest-∀ν-arrow-var-star-star-var-map f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-∀ν-arrow-var-star-star-var-map
      (map-ν-target∈ f) D⊑A D⊑B)

greatest-∀ν-arrow-star-var-var-star-map :
  ∀ {Φᴸ Φᴿ Φᴼ D} →
  ImpVarTargetMap Φᴿ Φᴼ 0 0 →
  0 ∣ Φᴸ ⊢ D ⊑ `∀ (★ ⇒ ＇ 0) →
  0 ∣ Φᴿ ⊢ D ⊑ ＇ 0 ⇒ ★ →
  0 ∣ Φᴼ ⊢ D ⊑ `∀ (＇ 1 ⇒ ＇ 0)
greatest-∀ν-arrow-star-var-var-star-map f (∀ⁱ D⊑A) (ν occD D⊑B) =
  ∀ⁱ
    (greatest-arrow-right-left-target-map
      plain-zero-target-map
      (right-zero-to-one-target-map f)
      D⊑A D⊑B)
greatest-∀ν-arrow-star-var-var-star-map f (ν occD D⊑A) (ν _ D⊑B) =
  ν occD
    (greatest-∀ν-arrow-star-var-var-star-map
      (map-ν-target∈ f) D⊑A D⊑B)

glbᶜ-lift-∀ν-arrow-var-star-star-var :
  Glbᶜ ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (`∀ (＇ 0 ⇒ ＇ 1)) (`∀ (＇ 0 ⇒ ★)) (★ ⇒ ＇ 0)
glbᶜ-lift-∀ν-arrow-var-star-star-var =
  glbᶜ-intro
    (∀ⁱ (lowerˡᶜ glbᶜ-arrow-var-star-star-var-nested))
    (ν refl (lowerʳᶜ glbᶜ-arrow-var-star-star-var-nested))
    (λ D D⊑A D⊑B →
      greatest-∀ν-arrow-var-star-star-var-map
        zero-target-single-map D⊑A D⊑B)

glbᶜ-lift-∀ν-arrow-star-var-var-star :
  Glbᶜ ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (`∀ (＇ 1 ⇒ ＇ 0)) (`∀ (★ ⇒ ＇ 0)) (＇ 0 ⇒ ★)
glbᶜ-lift-∀ν-arrow-star-var-var-star =
  glbᶜ-intro
    (∀ⁱ (lowerˡᶜ glbᶜ-arrow-star-var-var-star-nested))
    (ν refl (lowerʳᶜ glbᶜ-arrow-star-var-var-star-nested))
    (λ D D⊑A D⊑B →
      greatest-∀ν-arrow-star-var-var-star-map
        zero-target-single-map D⊑A D⊑B)

glbᶜ-arrow-var-star-star-base :
  ∀ {κ} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (＇ 0 ⇒ ‵ κ) (＇ 0 ⇒ ★) (★ ⇒ ‵ κ)
glbᶜ-arrow-var-star-star-base =
  glbᶜ-arrow-left-right-var-base-map
    (λ x → x)
    glbᶜ-var-star-single-core
    (glbᶜ-star-base
      {Φᴸ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴿ = (0 ˣ⊑★) ∷ []}
      {Φᴼ = (0 ˣ⊑ˣ 0) ∷ []})

occurs-zero-var-arrow-star : occurs zero (＇ 0 ⇒ ★) ≡ true
occurs-zero-var-arrow-star = refl

glbᶜ-lift-∀ν-arrow-var-base :
  ∀ {κ} →
  Glbᶜ [] [] [] (`∀ (＇ 0 ⇒ ‵ κ)) (`∀ (＇ 0 ⇒ ★)) (★ ⇒ ‵ κ)
glbᶜ-lift-∀ν-arrow-var-base =
  glbᶜ-intro
    (∀ⁱ (lowerˡᶜ glbᶜ-arrow-var-star-star-base))
    (ν occurs-zero-var-arrow-star (lowerʳᶜ glbᶜ-arrow-var-star-star-base))
    (λ D D⊑∀A D⊑B → greatest-∀ν-arrow-var-base D⊑∀A D⊑B)

glbᶜ-arrow-star-base-var-star :
  ∀ {κ} →
  Glbᶜ ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (＇ 0 ⇒ ‵ κ) (★ ⇒ ‵ κ) (＇ 0 ⇒ ★)
glbᶜ-arrow-star-base-var-star =
  glbᶜ-arrow-right-left-base-var-map
    (λ x → x)
    glbᶜ-star-var-single-core
    (glbᶜ-base-star
      {Φᴸ = (0 ˣ⊑★) ∷ []}
      {Φᴿ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴼ = (0 ˣ⊑ˣ 0) ∷ []})

glbᶜ-lift-ν∀-arrow-base-var :
  ∀ {κ} →
  Glbᶜ [] [] [] (`∀ (＇ 0 ⇒ ‵ κ)) (★ ⇒ ‵ κ) (`∀ (＇ 0 ⇒ ★))
glbᶜ-lift-ν∀-arrow-base-var =
  glbᶜ-intro
    (ν occurs-zero-var-arrow-star (lowerˡᶜ glbᶜ-arrow-star-base-var-star))
    (∀ⁱ (lowerʳᶜ glbᶜ-arrow-star-base-var-star))
    (λ D D⊑A D⊑∀B → greatest-ν∀-arrow-base-var D⊑A D⊑∀B)

glbᶜ-arrow-star-var-base-star :
  ∀ {κ} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (‵ κ ⇒ ＇ 0) (★ ⇒ ＇ 0) (‵ κ ⇒ ★)
glbᶜ-arrow-star-var-base-star =
  glbᶜ-arrow-right-left-base-var-from-left
    (λ x → x)
    (glbᶜ-star-base
      {Φᴸ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴿ = (0 ˣ⊑★) ∷ []}
      {Φᴼ = (0 ˣ⊑ˣ 0) ∷ []})
    glbᶜ-var-star-single-core

occurs-zero-star-arrow-var : occurs zero (★ ⇒ ＇ 0) ≡ true
occurs-zero-star-arrow-var = refl

glbᶜ-lift-∀ν-arrow-var-codomain :
  ∀ {κ} →
  Glbᶜ [] [] [] (`∀ (‵ κ ⇒ ＇ 0)) (`∀ (★ ⇒ ＇ 0)) (‵ κ ⇒ ★)
glbᶜ-lift-∀ν-arrow-var-codomain =
  glbᶜ-intro
    (∀ⁱ (lowerˡᶜ glbᶜ-arrow-star-var-base-star))
    (ν occurs-zero-star-arrow-var (lowerʳᶜ glbᶜ-arrow-star-var-base-star))
    (λ D D⊑∀A D⊑B → greatest-∀ν-arrow-var-codomain D⊑∀A D⊑B)

glbᶜ-arrow-base-star-star-var :
  ∀ {κ} →
  Glbᶜ ((0 ˣ⊑★) ∷ []) ((0 ˣ⊑ˣ 0) ∷ []) ((0 ˣ⊑ˣ 0) ∷ [])
       (‵ κ ⇒ ＇ 0) (‵ κ ⇒ ★) (★ ⇒ ＇ 0)
glbᶜ-arrow-base-star-star-var =
  glbᶜ-arrow-left-right-base-var-from-right
    (λ x → x)
    (glbᶜ-base-star
      {Φᴸ = (0 ˣ⊑★) ∷ []}
      {Φᴿ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴼ = (0 ˣ⊑ˣ 0) ∷ []})
    glbᶜ-star-var-single-core

glbᶜ-lift-ν∀-arrow-var-codomain :
  ∀ {κ} →
  Glbᶜ [] [] [] (`∀ (‵ κ ⇒ ＇ 0)) (‵ κ ⇒ ★) (`∀ (★ ⇒ ＇ 0))
glbᶜ-lift-ν∀-arrow-var-codomain =
  glbᶜ-intro
    (ν occurs-zero-star-arrow-var (lowerˡᶜ glbᶜ-arrow-base-star-star-var))
    (∀ⁱ (lowerʳᶜ glbᶜ-arrow-base-star-star-var))
    (λ D D⊑A D⊑∀B → greatest-ν∀-arrow-var-codomain D⊑A D⊑∀B)

record Lift⊓∀∀Support
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B C : Ty) : Set where
  field
    k∀ν :
      ∀ {D} →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
      occurs zero D ≡ true →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

    kν∀ :
      ∀ {D} →
      occurs zero D ≡ true →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

    kνν :
      ∀ {D} →
      occurs zero D ≡ true →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

open Lift⊓∀∀Support public

lift-⊓-∀∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  Lift⊓∀∀Support Φᴸ Φᴿ Φᴼ A B C →
  GlbSearch (`∀ A) (`∀ B)
lift-⊓-∀∀ glb support =
  glb-search _ _ _ _
    (glbᶜ-lift-∀∀-open glb
      (k∀ν support)
      (kν∀ support)
      (kνν support))

record Lift⊓∀νSupport
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B C : Ty) : Set where
  field
    k∀∀ʳ :
      ∀ {D B′} →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B′ →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

    kνˡ :
      ∀ {D} →
      occurs zero D ≡ true →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ ⊢ D ⊑ `∀ A →
      0 ∣ Φᴿ ⊢ `∀ D ⊑ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

open Lift⊓∀νSupport public

lift-⊓-∀ν :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero A ≡ true →
  Glbᶜ ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ)
       ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  Lift⊓∀νSupport Φᴸ Φᴿ Φᴼ A B C →
  GlbSearch (`∀ A) B
lift-⊓-∀ν occA glb support =
  glb-search _ _ _ _
    (glbᶜ-lift-∀ν-open occA glb
      (k∀∀ʳ support)
      (kνˡ support))

record Lift⊓ν∀Support
    (Φᴸ Φᴿ Φᴼ : ImpCtx) (A B C : Ty) : Set where
  field
    k∀∀ˡ :
      ∀ {D A′} →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴸ ⊢ D ⊑ A′ →
      0 ∣ (0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ ⊢ D ⊑ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

    kνʳ :
      ∀ {D} →
      occurs zero D ≡ true →
      0 ∣ Φᴸ ⊢ `∀ D ⊑ A →
      0 ∣ (0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴿ ⊢ D ⊑ `∀ B →
      0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ C

open Lift⊓ν∀Support public

left-∀∀-support :
  ∀ {Φᴸ Φᴿ A B} →
  Lift⊓∀∀Support Φᴸ Φᴿ Φᴸ A B A
left-∀∀-support .k∀ν D⊑A occD D⊑∀B = ∀ⁱ D⊑A
left-∀∀-support .kν∀ occD D⊑∀A D⊑B = ν occD D⊑∀A
left-∀∀-support .kνν occD D⊑∀A D⊑∀B = ν occD D⊑∀A

right-∀∀-support :
  ∀ {Φᴸ Φᴿ A B} →
  Lift⊓∀∀Support Φᴸ Φᴿ Φᴿ A B B
right-∀∀-support .k∀ν D⊑A occD D⊑∀B = ν occD D⊑∀B
right-∀∀-support .kν∀ occD D⊑∀A D⊑B = ∀ⁱ D⊑B
right-∀∀-support .kνν occD D⊑∀A D⊑∀B = ν occD D⊑∀B

left-∀ν-support :
  ∀ {Φᴸ Φᴿ A B} →
  Lift⊓∀νSupport Φᴸ Φᴿ Φᴸ A B A
left-∀ν-support .k∀∀ʳ D⊑A D⊑B′ = ∀ⁱ D⊑A
left-∀ν-support .kνˡ occD D⊑∀A ∀D⊑B = ν occD D⊑∀A

right-ν∀-support :
  ∀ {Φᴸ Φᴿ A B} →
  Lift⊓ν∀Support Φᴸ Φᴿ Φᴿ A B B
right-ν∀-support .k∀∀ˡ D⊑A′ D⊑B = ∀ⁱ D⊑B
right-ν∀-support .kνʳ occD ∀D⊑A D⊑∀B = ν occD D⊑∀B

mutual
  base-base-left-right-k∀ν :
    ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D ι κ} →
    0 ∣ Φᴸ ⊢ D ⊑ ‵ ι ⇒ A₂ →
    occurs zero D ≡ true →
    0 ∣ Φᴿ ⊢ D ⊑ `∀ (B₁ ⇒ ‵ κ) →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-left-right-k∀ν D⊑A occD D⊑∀B
      with arrow∀-lower²-inv D⊑A D⊑∀B
  base-base-left-right-k∀ν D⊑A occD D⊑∀B
      | via-arrow∀ occC C⊑A C⊑B =
        ν occD (∀ⁱ (greatest-arrow-left-right-base-base C⊑A C⊑B))
  base-base-left-right-k∀ν D⊑A occD D⊑∀B
      | via-arrowν occC C⊑A C⊑∀B =
        ν occD (base-base-left-right-k∀ν C⊑A occC C⊑∀B)

  base-base-left-right-kν∀ :
    ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D ι κ} →
    occurs zero D ≡ true →
    0 ∣ Φᴸ ⊢ D ⊑ `∀ (‵ ι ⇒ A₂) →
    0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ ‵ κ →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-left-right-kν∀ occD D⊑∀A D⊑B
      with ∀arrow-lower²-inv D⊑∀A D⊑B
  base-base-left-right-kν∀ occD D⊑∀A D⊑B
      | via-∀arrow C⊑A occC C⊑B =
        ν occD (∀ⁱ (greatest-arrow-left-right-base-base C⊑A C⊑B))
  base-base-left-right-kν∀ occD D⊑∀A D⊑B
      | via-νarrow occC C⊑∀A C⊑B =
        ν occD (base-base-left-right-kν∀ occC C⊑∀A C⊑B)

  base-base-left-right-kνν :
    ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ D ι κ} →
    occurs zero D ≡ true →
    0 ∣ Φᴸ ⊢ D ⊑ `∀ (‵ ι ⇒ A₂) →
    0 ∣ Φᴿ ⊢ D ⊑ `∀ (B₁ ⇒ ‵ κ) →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-left-right-kνν occD (∀ⁱ C⊑A) (∀ⁱ C⊑B) =
    ν occD (∀ⁱ (greatest-arrow-left-right-base-base C⊑A C⊑B))
  base-base-left-right-kνν occD (∀ⁱ C⊑A) (ν occC C⊑∀B) =
    ν occD (base-base-left-right-k∀ν C⊑A occC C⊑∀B)
  base-base-left-right-kνν occD (ν occC C⊑∀A) (∀ⁱ C⊑B) =
    ν occD (base-base-left-right-kν∀ occC C⊑∀A C⊑B)
  base-base-left-right-kνν occD (ν occC C⊑∀A) (ν _ C⊑∀B) =
    ν occD (base-base-left-right-kνν occC C⊑∀A C⊑∀B)

base-base-left-right-∀∀-support :
  ∀ {Φᴸ Φᴿ Φᴼ A₂ B₁ ι κ} →
  Lift⊓∀∀Support Φᴸ Φᴿ Φᴼ (‵ ι ⇒ A₂) (B₁ ⇒ ‵ κ) (‵ ι ⇒ ‵ κ)
base-base-left-right-∀∀-support .k∀ν D⊑A occD D⊑∀B =
  base-base-left-right-k∀ν D⊑A occD D⊑∀B
base-base-left-right-∀∀-support .kν∀ occD D⊑∀A D⊑B =
  base-base-left-right-kν∀ occD D⊑∀A D⊑B
base-base-left-right-∀∀-support .kνν occD D⊑∀A D⊑∀B =
  base-base-left-right-kνν occD D⊑∀A D⊑∀B

mutual
  base-base-right-left-k∀ν :
    ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D ι κ} →
    0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ ‵ κ →
    occurs zero D ≡ true →
    0 ∣ Φᴿ ⊢ D ⊑ `∀ (‵ ι ⇒ B₂) →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-right-left-k∀ν D⊑A occD D⊑∀B
      with arrow∀-lower²-inv D⊑A D⊑∀B
  base-base-right-left-k∀ν D⊑A occD D⊑∀B
      | via-arrow∀ occC C⊑A C⊑B =
        ν occD (∀ⁱ (greatest-arrow-right-left-base-base C⊑A C⊑B))
  base-base-right-left-k∀ν D⊑A occD D⊑∀B
      | via-arrowν occC C⊑A C⊑∀B =
        ν occD (base-base-right-left-k∀ν C⊑A occC C⊑∀B)

  base-base-right-left-kν∀ :
    ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D ι κ} →
    occurs zero D ≡ true →
    0 ∣ Φᴸ ⊢ D ⊑ `∀ (A₁ ⇒ ‵ κ) →
    0 ∣ Φᴿ ⊢ D ⊑ ‵ ι ⇒ B₂ →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-right-left-kν∀ occD D⊑∀A D⊑B
      with ∀arrow-lower²-inv D⊑∀A D⊑B
  base-base-right-left-kν∀ occD D⊑∀A D⊑B
      | via-∀arrow C⊑A occC C⊑B =
        ν occD (∀ⁱ (greatest-arrow-right-left-base-base C⊑A C⊑B))
  base-base-right-left-kν∀ occD D⊑∀A D⊑B
      | via-νarrow occC C⊑∀A C⊑B =
        ν occD (base-base-right-left-kν∀ occC C⊑∀A C⊑B)

  base-base-right-left-kνν :
    ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ D ι κ} →
    occurs zero D ≡ true →
    0 ∣ Φᴸ ⊢ D ⊑ `∀ (A₁ ⇒ ‵ κ) →
    0 ∣ Φᴿ ⊢ D ⊑ `∀ (‵ ι ⇒ B₂) →
    0 ∣ Φᴼ ⊢ `∀ D ⊑ `∀ (‵ ι ⇒ ‵ κ)
  base-base-right-left-kνν occD (∀ⁱ C⊑A) (∀ⁱ C⊑B) =
    ν occD (∀ⁱ (greatest-arrow-right-left-base-base C⊑A C⊑B))
  base-base-right-left-kνν occD (∀ⁱ C⊑A) (ν occC C⊑∀B) =
    ν occD (base-base-right-left-k∀ν C⊑A occC C⊑∀B)
  base-base-right-left-kνν occD (ν occC C⊑∀A) (∀ⁱ C⊑B) =
    ν occD (base-base-right-left-kν∀ occC C⊑∀A C⊑B)
  base-base-right-left-kνν occD (ν occC C⊑∀A) (ν _ C⊑∀B) =
    ν occD (base-base-right-left-kνν occC C⊑∀A C⊑∀B)

base-base-right-left-∀∀-support :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ B₂ ι κ} →
  Lift⊓∀∀Support Φᴸ Φᴿ Φᴼ (A₁ ⇒ ‵ κ) (‵ ι ⇒ B₂) (‵ ι ⇒ ‵ κ)
base-base-right-left-∀∀-support .k∀ν D⊑A occD D⊑∀B =
  base-base-right-left-k∀ν D⊑A occD D⊑∀B
base-base-right-left-∀∀-support .kν∀ occD D⊑∀A D⊑B =
  base-base-right-left-kν∀ occD D⊑∀A D⊑B
base-base-right-left-∀∀-support .kνν occD D⊑∀A D⊑∀B =
  base-base-right-left-kνν occD D⊑∀A D⊑∀B

lift-⊓-ν∀ :
  ∀ {Φᴸ Φᴿ Φᴼ A B C} →
  occurs zero B ≡ true →
  Glbᶜ ((0 ˣ⊑★) ∷ ⇑ᴸᵢ Φᴸ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴿ)
       ((0 ˣ⊑ˣ 0) ∷ ⇑ᵢ Φᴼ)
       C A B →
  Lift⊓ν∀Support Φᴸ Φᴿ Φᴼ A B C →
  GlbSearch A (`∀ B)
lift-⊓-ν∀ occB glb support =
  glb-search _ _ _ _
    (glbᶜ-lift-ν∀-open occB glb
      (k∀∀ˡ support)
      (kνʳ support))

lift-search⁺ :
  ∀ (n m : ℕ) {A B} →
  GlbSearch⁺ A B →
  Maybe (GlbSearch⁺ (add∀ n A) (add∀ m B))
lift-search⁺ zero zero result = just result
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    with occurs zero B in occB | unshiftᴸᵢ Φᴸ′ | unshiftᵢ Φᴿ′
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | false | _ | _ = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | true | nothing | _ = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | true | _ | nothing = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR)
    with lift-search⁺ zero m
      (glb-right
        (glbᶜ-lift-ν∀-open occB
          (cast-Glbᶜ
            (cong (λ xs → (0 ˣ⊑★) ∷ xs) (sym eqL))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqR))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqR))
            glb)
          (k∀∀ˡ
            (right-ν∀-support {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}))
          (kνʳ
            (right-ν∀-support {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}))))
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR) | nothing = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑★) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR) | just result =
      just (cast-search⁺ʳ (add∀-step m B) result)
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    with occurs zero B in occB
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    | false = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    | true
    with lift-search⁺ zero m
      (glb-right
        (glbᶜ-lift-ν∀-open occB
          (glbᶜ-right-cons
            {aᴸ = 0 ˣ⊑★} {aᴿ = 0 ˣ⊑ˣ 0} glb)
          (k∀∀ˡ
            (right-ν∀-support {Φᴸ = []} {Φᴿ = []} {A = A} {B = B}))
          (kνʳ
            (right-ν∀-support {Φᴸ = []} {Φᴿ = []} {A = A} {B = B}))))
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    | true | nothing = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    | true | just result =
      just (cast-search⁺ʳ (add∀-step m B) result)
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = (0 ˣ⊑★) ∷ []} {Φᴿ₁ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ★} {A₂ = ‵ κ} {B₁ = ＇ 0} {B₂ = ★}
      glb₁ glb₂ glb)
    with lift-search⁺ zero m
      (glb-any (glbᶜ-lift-ν∀-arrow-base-var {κ = κ}))
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = (0 ˣ⊑★) ∷ []} {Φᴿ₁ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ★} {A₂ = ‵ κ} {B₁ = ＇ 0} {B₂ = ★}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = (0 ˣ⊑★) ∷ []} {Φᴿ₁ = (0 ˣ⊑ˣ 0) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ★} {A₂ = ‵ κ} {B₁ = ＇ 0} {B₂ = ★}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ʳ (add∀-step m (＇ 0 ⇒ ★)) result)
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑★) ∷ []} {Φᴿ₂ = (0 ˣ⊑ˣ 0) ∷ []}
      {A₁ = ‵ κ} {A₂ = ★} {B₁ = ★} {B₂ = ＇ 0}
      glb₁ glb₂ glb)
    with lift-search⁺ zero m
      (glb-any (glbᶜ-lift-ν∀-arrow-var-codomain {κ = κ}))
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑★) ∷ []} {Φᴿ₂ = (0 ˣ⊑ˣ 0) ∷ []}
      {A₁ = ‵ κ} {A₂ = ★} {B₁ = ★} {B₂ = ＇ 0}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ zero (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑★) ∷ []} {Φᴿ₂ = (0 ˣ⊑ˣ 0) ∷ []}
      {A₁ = ‵ κ} {A₂ = ★} {B₁ = ★} {B₂ = ＇ 0}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ʳ (add∀-step m (★ ⇒ ＇ 0)) result)
lift-search⁺ zero (suc m) result = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    with occurs zero A in occA | unshiftᵢ Φᴸ′ | unshiftᴸᵢ Φᴿ′
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | false | _ | _ = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | true | nothing | _ = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | true | _ | nothing = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR)
    with lift-search⁺ n zero
      (glb-left
        (glbᶜ-lift-∀ν-open occA
          (cast-Glbᶜ
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqL))
            (cong (λ xs → (0 ˣ⊑★) ∷ xs) (sym eqR))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqL))
            glb)
          (k∀∀ʳ
            (left-∀ν-support {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}))
          (kνˡ
            (left-∀ν-support {Φᴸ = Φᴸ} {Φᴿ = Φᴿ} {A = A} {B = B}))))
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR) | nothing = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑★) ∷ Φᴿ′} glb)
    | true | just (Φᴸ , eqL) | just (Φᴿ , eqR) | just result =
      just (cast-search⁺ˡ (add∀-step n A) result)
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    with occurs zero A in occA
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    | false = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    | true
    with lift-search⁺ n zero
      (glb-left
        (glbᶜ-lift-∀ν-open occA
          (glbᶜ-left-cons
            {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑★} glb)
          (k∀∀ʳ
            (left-∀ν-support {Φᴸ = []} {Φᴿ = []} {A = A} {B = B}))
          (kνˡ
            (left-∀ν-support {Φᴸ = []} {Φᴿ = []} {A = A} {B = B}))))
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    | true | nothing = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    | true | just result =
      just (cast-search⁺ˡ (add∀-step n A) result)
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₁ = (0 ˣ⊑★) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ＇ 0} {A₂ = ★} {B₁ = ★} {B₂ = ‵ κ}
      glb₁ glb₂ glb)
    with lift-search⁺ n zero
      (glb-any (glbᶜ-lift-∀ν-arrow-var-base {κ = κ}))
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₁ = (0 ˣ⊑★) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ＇ 0} {A₂ = ★} {B₁ = ★} {B₂ = ‵ κ}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₁ = (0 ˣ⊑★) ∷ []}
      {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ＇ 0} {A₂ = ★} {B₁ = ★} {B₂ = ‵ κ}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ˡ (add∀-step n (＇ 0 ⇒ ★)) result)
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₂ = (0 ˣ⊑★) ∷ []}
      {A₁ = ★} {A₂ = ＇ 0} {B₁ = ‵ κ} {B₂ = ★}
      glb₁ glb₂ glb)
    with lift-search⁺ n zero
      (glb-any (glbᶜ-lift-∀ν-arrow-var-codomain {κ = κ}))
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₂ = (0 ˣ⊑★) ∷ []}
      {A₁ = ★} {A₂ = ＇ 0} {B₁ = ‵ κ} {B₂ = ★}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ (suc n) zero {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []}
      {Φᴸ₂ = (0 ˣ⊑ˣ 0) ∷ []} {Φᴿ₂ = (0 ˣ⊑★) ∷ []}
      {A₁ = ★} {A₂ = ＇ 0} {B₁ = ‵ κ} {B₂ = ★}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ˡ (add∀-step n (★ ⇒ ＇ 0)) result)
lift-search⁺ (suc n) zero result = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    with unshiftᵢ Φᴸ′ | unshiftᵢ Φᴿ′
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | nothing | _ = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | _ | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR)
    with lift-search⁺ n m
      (glb-left
        (glbᶜ-lift-∀∀-open
          (cast-Glbᶜ
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqL))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqR))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqL))
            glb)
          (k∀ν left-∀∀-support)
          (kν∀ left-∀∀-support)
          (kνν left-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
              {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb)
    with lift-search⁺ n m
      (glb-left
        (glbᶜ-lift-∀∀-open
          (glbᶜ-left-cons
            {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb)
          (k∀ν left-∀∀-support)
          (kν∀ left-∀∀-support)
          (kνν left-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-left {Φᴸ = []} {Φᴿ = []} glb) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    with unshiftᵢ Φᴸ′ | unshiftᵢ Φᴿ′
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | nothing | _ = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | _ | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR)
    with lift-search⁺ n m
      (glb-right
        (glbᶜ-lift-∀∀-open
          (cast-Glbᶜ
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqL))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqR))
            (cong (λ xs → (0 ˣ⊑ˣ 0) ∷ xs) (sym eqR))
            glb)
          (k∀ν right-∀∀-support)
          (kν∀ right-∀∀-support)
          (kνν right-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = (0 ˣ⊑ˣ 0) ∷ Φᴸ′}
               {Φᴿ = (0 ˣ⊑ˣ 0) ∷ Φᴿ′} glb)
    | just (Φᴸ , eqL) | just (Φᴿ , eqR) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb)
    with lift-search⁺ n m
      (glb-right
        (glbᶜ-lift-∀∀-open
          (glbᶜ-right-cons
            {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb)
          (k∀ν right-∀∀-support)
          (kν∀ right-∀∀-support)
          (kνν right-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-right {Φᴸ = []} {Φᴿ = []} glb) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ‵ ι} {A₂ = A₂} {B₁ = B₁} {B₂ = ‵ κ}
      glb₁ glb₂ glb)
    with lift-search⁺ n m
      (glb-any
        (glbᶜ-lift-∀∀-open
          (glbᶜ-arrow-left-right-base-base
            (glbᶜ-left-cons
              {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb₁)
            (glbᶜ-right-cons
              {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb₂))
          (k∀ν base-base-left-right-∀∀-support)
          (kν∀ base-base-left-right-∀∀-support)
          (kνν base-base-left-right-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ‵ ι} {A₂ = A₂} {B₁ = B₁} {B₂ = ‵ κ}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-left-right
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = ‵ ι} {A₂ = A₂} {B₁ = B₁} {B₂ = ‵ κ}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = A₁} {A₂ = ‵ κ} {B₁ = ‵ ι} {B₂ = B₂}
      glb₁ glb₂ glb)
    with lift-search⁺ n m
      (glb-any
        (glbᶜ-lift-∀∀-open
          (glbᶜ-arrow-right-left-base-base
            (glbᶜ-right-cons
              {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb₁)
            (glbᶜ-left-cons
              {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0} glb₂))
          (k∀ν base-base-right-left-∀∀-support)
          (kν∀ base-base-right-left-∀∀-support)
          (kνν base-base-right-left-∀∀-support)))
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = A₁} {A₂ = ‵ κ} {B₁ = ‵ ι} {B₂ = B₂}
      glb₁ glb₂ glb) | nothing = nothing
lift-search⁺ (suc n) (suc m) {A = A} {B = B}
    (glb-mixed-right-left
      {Φᴸ₁ = []} {Φᴿ₁ = []} {Φᴸ₂ = []} {Φᴿ₂ = []}
      {A₁ = A₁} {A₂ = ‵ κ} {B₁ = ‵ ι} {B₂ = B₂}
      glb₁ glb₂ glb) | just result =
      just (cast-search⁺ʳ (add∀-step m B)
             (cast-search⁺ˡ (add∀-step n A) result))
lift-search⁺ (suc n) (suc m) result = nothing

closed-search⁺ :
  ∀ {A B} →
  GlbSearch⁺ A B →
  Maybe (GlbSearch⁺ A B)
closed-search⁺ (glb-left {Φᴸ = []} {Φᴿ = []} glb) =
  just (glb-left glb)
closed-search⁺ (glb-right {Φᴸ = []} {Φᴿ = []} glb) =
  just (glb-right glb)
closed-search⁺ (glb-any {Φᴸ = []} {Φᴿ = []} {Φᴼ = []} glb) =
  just (glb-any glb)
closed-search⁺
    (glb-mixed-left-right {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}
      glb₁ glb₂ glb) =
  just (glb-mixed-left-right glb₁ glb₂ glb)
closed-search⁺
    (glb-mixed-right-left {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}
      glb₁ glb₂ glb) =
  just (glb-mixed-right-left glb₁ glb₂ glb)
closed-search⁺ _ = nothing

glbᶜ-arrow-left :
  ∀ {Φᴸ Φᴿ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ Φᴿ Φᴸ A₁ A₁ B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴸ A₂ A₂ B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴸ (A₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A _ → D⊑A)

glbᶜ-arrow-right :
  ∀ {Φᴸ Φᴿ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ Φᴿ Φᴿ B₁ A₁ B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴿ B₂ A₂ B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴿ (B₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D _ D⊑B → D⊑B)

glbᶜ-arrow-left-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴸ₁ A₁ A₁ B₁ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴸ₂ A₂ A₂ B₂ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂) (Φᴸ₁ ++ Φᴸ₂)
       (A₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerˡᶜ glb₂))
    (weaken-⊑-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerʳᶜ glb₂))
    (λ D D⊑A _ → D⊑A)

glbᶜ-arrow-left-head-++ :
  ∀ {aᴸ aᴿ Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ (aᴸ ∷ Φᴸ₁) (aᴿ ∷ Φᴿ₁) (aᴸ ∷ Φᴸ₁) A₁ A₁ B₁ →
  Glbᶜ (aᴸ ∷ Φᴸ₂) (aᴿ ∷ Φᴿ₂) (aᴸ ∷ Φᴸ₂) A₂ A₂ B₂ →
  Glbᶜ (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂)) (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂))
       (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂))
       (A₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left-head-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerˡᶜ glb₂))
    (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerʳᶜ glb₂))
    (λ D D⊑A _ → D⊑A)

glbᶜ-arrow-right-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴿ₁ B₁ A₁ B₁ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴿ₂ B₂ A₂ B₂ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂) (Φᴿ₁ ++ Φᴿ₂)
       (B₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerˡᶜ glb₂))
    (weaken-⊑-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerʳᶜ glb₂))
    (λ D _ D⊑B → D⊑B)

glbᶜ-arrow-right-head-++ :
  ∀ {aᴸ aᴿ Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ (aᴸ ∷ Φᴸ₁) (aᴿ ∷ Φᴿ₁) (aᴿ ∷ Φᴿ₁) B₁ A₁ B₁ →
  Glbᶜ (aᴸ ∷ Φᴸ₂) (aᴿ ∷ Φᴿ₂) (aᴿ ∷ Φᴿ₂) B₂ A₂ B₂ →
  Glbᶜ (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂)) (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂))
       (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂))
       (B₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right-head-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerˡᶜ glb₂))
    (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerʳᶜ glb₂))
    (λ D _ D⊑B → D⊑B)

greatest-arrow-left-right-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ A₂ B₁ B₂ D} →
  ImpCtxMap Φᴸ Φᴼ →
  ImpCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ A₁ ⇒ B₂
greatest-arrow-left-right-map f g (D⊑A₁ ↦ D⊑A₂) (D⊑B₁ ↦ D⊑B₂) =
  map-⊑ f D⊑A₁ ↦ map-⊑ g D⊑B₂
greatest-arrow-left-right-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-left-right-map (map-νᵢ f) (map-νᵢ g) D⊑A D⊑B)

greatest-arrow-right-left-map :
  ∀ {Φᴸ Φᴿ Φᴼ A₁ A₂ B₁ B₂ D} →
  ImpCtxMap Φᴸ Φᴼ →
  ImpCtxMap Φᴿ Φᴼ →
  0 ∣ Φᴸ ⊢ D ⊑ A₁ ⇒ A₂ →
  0 ∣ Φᴿ ⊢ D ⊑ B₁ ⇒ B₂ →
  0 ∣ Φᴼ ⊢ D ⊑ B₁ ⇒ A₂
greatest-arrow-right-left-map f g (D⊑A₁ ↦ D⊑A₂) (D⊑B₁ ↦ D⊑B₂) =
  map-⊑ g D⊑B₁ ↦ map-⊑ f D⊑A₂
greatest-arrow-right-left-map f g (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-right-left-map (map-νᵢ f) (map-νᵢ g) D⊑A D⊑B)

greatest-arrow-left-right :
  ∀ {Φ A₁ A₂ B₁ B₂ D} →
  0 ∣ Φ ⊢ D ⊑ A₁ ⇒ A₂ →
  0 ∣ Φ ⊢ D ⊑ B₁ ⇒ B₂ →
  0 ∣ Φ ⊢ D ⊑ A₁ ⇒ B₂
greatest-arrow-left-right (D⊑A₁ ↦ D⊑A₂) (D⊑B₁ ↦ D⊑B₂) =
  D⊑A₁ ↦ D⊑B₂
greatest-arrow-left-right (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-left-right D⊑A D⊑B)

greatest-arrow-right-left :
  ∀ {Φ A₁ A₂ B₁ B₂ D} →
  0 ∣ Φ ⊢ D ⊑ A₁ ⇒ A₂ →
  0 ∣ Φ ⊢ D ⊑ B₁ ⇒ B₂ →
  0 ∣ Φ ⊢ D ⊑ B₁ ⇒ A₂
greatest-arrow-right-left (D⊑A₁ ↦ D⊑A₂) (D⊑B₁ ↦ D⊑B₂) =
  D⊑B₁ ↦ D⊑A₂
greatest-arrow-right-left (ν occD D⊑A) (ν _ D⊑B) =
  ν occD (greatest-arrow-right-left D⊑A D⊑B)

glbᶜ-arrow-left-right :
  ∀ {A₁ A₂ B₁ B₂} →
  Glbᶜ [] [] [] A₁ A₁ B₁ →
  Glbᶜ [] [] [] B₂ A₂ B₂ →
  Glbᶜ [] [] [] (A₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left-right glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B → greatest-arrow-left-right D⊑A D⊑B)

glbᶜ-arrow-right-left :
  ∀ {A₁ A₂ B₁ B₂} →
  Glbᶜ [] [] [] B₁ A₁ B₁ →
  Glbᶜ [] [] [] A₂ A₂ B₂ →
  Glbᶜ [] [] [] (B₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right-left glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D D⊑A D⊑B → greatest-arrow-right-left D⊑A D⊑B)

glbᶜ-arrow-left-right-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴸ₁ A₁ A₁ B₁ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴿ₂ B₂ A₂ B₂ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂)
       ((Φᴸ₁ ++ Φᴸ₂) ++ (Φᴿ₁ ++ Φᴿ₂))
       (A₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left-right-++ {Φᴸ₁ = Φᴸ₁} {Φᴿ₁ = Φᴿ₁}
    {Φᴸ₂ = Φᴸ₂}
    glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-++ʳ Φᴸ₁ (lowerˡᶜ glb₂))
    (weaken-⊑-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-++ʳ Φᴿ₁ (lowerʳᶜ glb₂))
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-map
        ∈-++ˡ
        (∈-++ʳ (Φᴸ₁ ++ Φᴸ₂))
        D⊑A D⊑B)

glbᶜ-arrow-left-right-head-++ :
  ∀ {a Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ (a ∷ Φᴸ₁) (a ∷ Φᴿ₁) (a ∷ Φᴸ₁) A₁ A₁ B₁ →
  Glbᶜ (a ∷ Φᴸ₂) (a ∷ Φᴿ₂) (a ∷ Φᴿ₂) B₂ A₂ B₂ →
  Glbᶜ (a ∷ (Φᴸ₁ ++ Φᴸ₂)) (a ∷ (Φᴿ₁ ++ Φᴿ₂))
       (a ∷ ((Φᴸ₁ ++ Φᴸ₂) ++ (Φᴿ₁ ++ Φᴿ₂)))
       (A₁ ⇒ B₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-left-right-head-++ {Φᴸ₁ = Φᴸ₁} {Φᴿ₁ = Φᴿ₁}
    {Φᴸ₂ = Φᴸ₂} {Φᴿ₂ = Φᴿ₂} glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerˡᶜ glb₂))
    (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerʳᶜ glb₂))
    (λ D D⊑A D⊑B →
      greatest-arrow-left-right-map
        head-++ˡ
        (head-++ʳ {Φ = Φᴸ₁ ++ Φᴸ₂} {Φ′ = Φᴿ₁ ++ Φᴿ₂})
        D⊑A D⊑B)

glbᶜ-arrow-right-left-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴿ₁ B₁ A₁ B₁ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴸ₂ A₂ A₂ B₂ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂)
       ((Φᴿ₁ ++ Φᴿ₂) ++ (Φᴸ₁ ++ Φᴸ₂))
       (B₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right-left-++ {Φᴸ₁ = Φᴸ₁} {Φᴿ₁ = Φᴿ₁}
    {Φᴿ₂ = Φᴿ₂}
    glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-++ʳ Φᴸ₁ (lowerˡᶜ glb₂))
    (weaken-⊑-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-++ʳ Φᴿ₁ (lowerʳᶜ glb₂))
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-map
        (∈-++ʳ (Φᴿ₁ ++ Φᴿ₂))
        ∈-++ˡ
        D⊑A D⊑B)

glbᶜ-arrow-right-left-head-++ :
  ∀ {a Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂ B₁ B₂} →
  Glbᶜ (a ∷ Φᴸ₁) (a ∷ Φᴿ₁) (a ∷ Φᴿ₁) B₁ A₁ B₁ →
  Glbᶜ (a ∷ Φᴸ₂) (a ∷ Φᴿ₂) (a ∷ Φᴸ₂) A₂ A₂ B₂ →
  Glbᶜ (a ∷ (Φᴸ₁ ++ Φᴸ₂)) (a ∷ (Φᴿ₁ ++ Φᴿ₂))
       (a ∷ ((Φᴿ₁ ++ Φᴿ₂) ++ (Φᴸ₁ ++ Φᴸ₂)))
       (B₁ ⇒ A₂) (A₁ ⇒ A₂) (B₁ ⇒ B₂)
glbᶜ-arrow-right-left-head-++ {Φᴸ₁ = Φᴸ₁} {Φᴿ₁ = Φᴿ₁}
    {Φᴸ₂ = Φᴸ₂} {Φᴿ₂ = Φᴿ₂} glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerˡᶜ glb₂))
    (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerʳᶜ glb₂))
    (λ D D⊑A D⊑B →
      greatest-arrow-right-left-map
        (head-++ʳ {Φ = Φᴿ₁ ++ Φᴿ₂} {Φ′ = Φᴸ₁ ++ Φᴸ₂})
        head-++ˡ
        D⊑A D⊑B)

closed-star-right? :
  ∀ B →
  GlbSearch⁺ ★ B →
  Maybe (Glbᶜ [] [] [] B ★ B)
closed-star-right? ★ (glb-left {Φᴸ = []} {Φᴿ = []} glb) = just glb
closed-star-right? B (glb-right {Φᴸ = []} {Φᴿ = []} glb) = just glb
closed-star-right? _ _ = nothing

glbᶜ-arrow-star-left :
  ∀ {Φᴸ Φᴿ A₁ A₂} →
  Glbᶜ Φᴸ Φᴿ Φᴸ A₁ A₁ ★ →
  Glbᶜ Φᴸ Φᴿ Φᴸ A₂ A₂ ★ →
  Glbᶜ Φᴸ Φᴿ Φᴸ (A₁ ⇒ A₂) (A₁ ⇒ A₂) ★
glbᶜ-arrow-star-left glb₁ glb₂ =
  glbᶜ-intro
    (lowerˡᶜ glb₁ ↦ lowerˡᶜ glb₂)
    (tag_⇒_ (lowerʳᶜ glb₁) (lowerʳᶜ glb₂))
    (λ D D⊑A _ → D⊑A)

glbᶜ-arrow-star-left-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴸ₁ A₁ A₁ ★ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴸ₂ A₂ A₂ ★ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂) (Φᴸ₁ ++ Φᴸ₂)
       (A₁ ⇒ A₂) (A₁ ⇒ A₂) ★
glbᶜ-arrow-star-left-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerˡᶜ glb₂))
    (tag_⇒_
      (weaken-⊑-++ˡ (lowerʳᶜ glb₁))
      (weaken-⊑-++ʳ _ (lowerʳᶜ glb₂)))
    (λ D D⊑A _ → D⊑A)

glbᶜ-arrow-star-left-head-++ :
  ∀ {aᴸ aᴿ Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ A₁ A₂} →
  Glbᶜ (aᴸ ∷ Φᴸ₁) (aᴿ ∷ Φᴿ₁) (aᴸ ∷ Φᴸ₁) A₁ A₁ ★ →
  Glbᶜ (aᴸ ∷ Φᴸ₂) (aᴿ ∷ Φᴿ₂) (aᴸ ∷ Φᴸ₂) A₂ A₂ ★ →
  Glbᶜ (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂)) (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂))
       (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂)) (A₁ ⇒ A₂) (A₁ ⇒ A₂) ★
glbᶜ-arrow-star-left-head-++ glb₁ glb₂ =
  glbᶜ-intro
    (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerˡᶜ glb₂))
    (tag_⇒_
      (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁))
      (weaken-⊑-head-++ʳ (lowerʳᶜ glb₂)))
    (λ D D⊑A _ → D⊑A)

glbᶜ-star-arrow-right :
  ∀ {Φᴸ Φᴿ B₁ B₂} →
  Glbᶜ Φᴸ Φᴿ Φᴿ B₁ ★ B₁ →
  Glbᶜ Φᴸ Φᴿ Φᴿ B₂ ★ B₂ →
  Glbᶜ Φᴸ Φᴿ Φᴿ (B₁ ⇒ B₂) ★ (B₁ ⇒ B₂)
glbᶜ-star-arrow-right glb₁ glb₂ =
  glbᶜ-intro
    (tag_⇒_ (lowerˡᶜ glb₁) (lowerˡᶜ glb₂))
    (lowerʳᶜ glb₁ ↦ lowerʳᶜ glb₂)
    (λ D _ D⊑B → D⊑B)

glbᶜ-star-arrow-right-++ :
  ∀ {Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ B₁ B₂} →
  Glbᶜ Φᴸ₁ Φᴿ₁ Φᴿ₁ B₁ ★ B₁ →
  Glbᶜ Φᴸ₂ Φᴿ₂ Φᴿ₂ B₂ ★ B₂ →
  Glbᶜ (Φᴸ₁ ++ Φᴸ₂) (Φᴿ₁ ++ Φᴿ₂) (Φᴿ₁ ++ Φᴿ₂)
       (B₁ ⇒ B₂) ★ (B₁ ⇒ B₂)
glbᶜ-star-arrow-right-++ glb₁ glb₂ =
  glbᶜ-intro
    (tag_⇒_
      (weaken-⊑-++ˡ (lowerˡᶜ glb₁))
      (weaken-⊑-++ʳ _ (lowerˡᶜ glb₂)))
    (weaken-⊑-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-++ʳ _ (lowerʳᶜ glb₂))
    (λ D _ D⊑B → D⊑B)

glbᶜ-star-arrow-right-head-++ :
  ∀ {aᴸ aᴿ Φᴸ₁ Φᴿ₁ Φᴸ₂ Φᴿ₂ B₁ B₂} →
  Glbᶜ (aᴸ ∷ Φᴸ₁) (aᴿ ∷ Φᴿ₁) (aᴿ ∷ Φᴿ₁) B₁ ★ B₁ →
  Glbᶜ (aᴸ ∷ Φᴸ₂) (aᴿ ∷ Φᴿ₂) (aᴿ ∷ Φᴿ₂) B₂ ★ B₂ →
  Glbᶜ (aᴸ ∷ (Φᴸ₁ ++ Φᴸ₂)) (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂))
       (aᴿ ∷ (Φᴿ₁ ++ Φᴿ₂)) (B₁ ⇒ B₂) ★ (B₁ ⇒ B₂)
glbᶜ-star-arrow-right-head-++ glb₁ glb₂ =
  glbᶜ-intro
    (tag_⇒_
      (weaken-⊑-head-++ˡ (lowerˡᶜ glb₁))
      (weaken-⊑-head-++ʳ (lowerˡᶜ glb₂)))
    (weaken-⊑-head-++ˡ (lowerʳᶜ glb₁) ↦
     weaken-⊑-head-++ʳ (lowerʳᶜ glb₂))
    (λ D _ D⊑B → D⊑B)

arrow-left-search? :
  ∀ {A₁ A₂ B₁ B₂} →
  GlbSearch⁺ A₁ B₁ →
  GlbSearch⁺ A₂ B₂ →
  Maybe (GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂))
arrow-left-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    with Φᴸ₁ ≟ImpCtx Φᴸ₂ | Φᴿ₁ ≟ImpCtx Φᴿ₂
arrow-left-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | yes eqL | yes eqR =
      just (glb-left
        (glbᶜ-arrow-left glb₁
          (cast-Glbᶜ (sym eqL) (sym eqR) (sym eqL) glb₂)))
arrow-left-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ with aᴸ₁ ≟ImpAssm aᴸ₂ | aᴿ₁ ≟ImpAssm aᴿ₂
arrow-left-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = .aᴸ₁ ∷ Φᴸ₂} {Φᴿ = .aᴿ₁ ∷ Φᴿ₂} glb₂)
    | _ | _ | yes refl | yes refl =
      just (glb-left (glbᶜ-arrow-left-head-++ glb₁ glb₂))
arrow-left-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ | _ = just (glb-left (glbᶜ-arrow-left-++ glb₁ glb₂))
arrow-left-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | _ | _ = just (glb-left (glbᶜ-arrow-left-++ glb₁ glb₂))
arrow-left-search? _ _ = nothing

arrow-right-search? :
  ∀ {A₁ A₂ B₁ B₂} →
  GlbSearch⁺ A₁ B₁ →
  GlbSearch⁺ A₂ B₂ →
  Maybe (GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂))
arrow-right-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    with Φᴸ₁ ≟ImpCtx Φᴸ₂ | Φᴿ₁ ≟ImpCtx Φᴿ₂
arrow-right-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | yes eqL | yes eqR =
      just (glb-right
        (glbᶜ-arrow-right glb₁
          (cast-Glbᶜ (sym eqL) (sym eqR) (sym eqR) glb₂)))
arrow-right-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ with aᴸ₁ ≟ImpAssm aᴸ₂ | aᴿ₁ ≟ImpAssm aᴿ₂
arrow-right-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = .aᴸ₁ ∷ Φᴸ₂} {Φᴿ = .aᴿ₁ ∷ Φᴿ₂} glb₂)
    | _ | _ | yes refl | yes refl =
      just (glb-right (glbᶜ-arrow-right-head-++ glb₁ glb₂))
arrow-right-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ | _ = just (glb-right (glbᶜ-arrow-right-++ glb₁ glb₂))
arrow-right-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | _ | _ = just (glb-right (glbᶜ-arrow-right-++ glb₁ glb₂))
arrow-right-search? _ _ = nothing

arrow-mixed-search? :
  ∀ {A₁ A₂ B₁ B₂} →
  GlbSearch⁺ A₁ B₁ →
  GlbSearch⁺ A₂ B₂ →
  Maybe (GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂))
arrow-mixed-search?
    (glb-left {Φᴸ = []} {Φᴿ = []} glb₁)
    (glb-right {Φᴸ = []} {Φᴿ = []} glb₂) =
  just (glb-mixed-left-right glb₁ glb₂
          (glbᶜ-arrow-left-right glb₁ glb₂))
arrow-mixed-search?
    (glb-right {Φᴸ = []} {Φᴿ = []} glb₁)
    (glb-left {Φᴸ = []} {Φᴿ = []} glb₂) =
  just (glb-mixed-right-left glb₁ glb₂
          (glbᶜ-arrow-right-left glb₁ glb₂))
arrow-mixed-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    with aᴸ₁ ≟ImpAssm aᴿ₁ | aᴸ₁ ≟ImpAssm aᴸ₂
       | aᴸ₁ ≟ImpAssm aᴿ₂
arrow-mixed-search?
    (glb-left {Φᴸ = a ∷ Φᴸ₁} {Φᴿ = .a ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = .a ∷ Φᴸ₂} {Φᴿ = .a ∷ Φᴿ₂} glb₂)
    | yes refl | yes refl | yes refl =
      just (glb-mixed-left-right glb₁ glb₂
              (glbᶜ-arrow-left-right-head-++ glb₁ glb₂))
arrow-mixed-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ =
      just (glb-mixed-left-right glb₁ glb₂
              (glbᶜ-arrow-left-right-++ glb₁ glb₂))
arrow-mixed-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    with aᴸ₁ ≟ImpAssm aᴿ₁ | aᴸ₁ ≟ImpAssm aᴸ₂
       | aᴸ₁ ≟ImpAssm aᴿ₂
arrow-mixed-search?
    (glb-right {Φᴸ = a ∷ Φᴸ₁} {Φᴿ = .a ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = .a ∷ Φᴸ₂} {Φᴿ = .a ∷ Φᴿ₂} glb₂)
    | yes refl | yes refl | yes refl =
      just (glb-mixed-right-left glb₁ glb₂
              (glbᶜ-arrow-right-left-head-++ glb₁ glb₂))
arrow-mixed-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ =
      just (glb-mixed-right-left glb₁ glb₂
              (glbᶜ-arrow-right-left-++ glb₁ glb₂))
arrow-mixed-search? (glb-left glb₁) (glb-right glb₂) =
  just (glb-mixed-left-right glb₁ glb₂
          (glbᶜ-arrow-left-right-++ glb₁ glb₂))
arrow-mixed-search? (glb-right glb₁) (glb-left glb₂) =
  just (glb-mixed-right-left glb₁ glb₂
          (glbᶜ-arrow-right-left-++ glb₁ glb₂))
arrow-mixed-search? _ _ = nothing

arrow-search? :
  ∀ {A₁ A₂ B₁ B₂} →
  GlbSearch⁺ A₁ B₁ →
  GlbSearch⁺ A₂ B₂ →
  Maybe (GlbSearch⁺ (A₁ ⇒ A₂) (B₁ ⇒ B₂))
arrow-search? result₁ result₂ with arrow-left-search? result₁ result₂
arrow-search? result₁ result₂ | just result = just result
arrow-search? result₁ result₂ | nothing
    with arrow-right-search? result₁ result₂
arrow-search? result₁ result₂ | nothing | just result = just result
arrow-search? result₁ result₂ | nothing | nothing =
  arrow-mixed-search? result₁ result₂

arrow-star-search? :
  ∀ {A₁ A₂} →
  GlbSearch⁺ A₁ ★ →
  GlbSearch⁺ A₂ ★ →
  Maybe (GlbSearch⁺ (A₁ ⇒ A₂) ★)
arrow-star-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    with Φᴸ₁ ≟ImpCtx Φᴸ₂ | Φᴿ₁ ≟ImpCtx Φᴿ₂
arrow-star-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | yes eqL | yes eqR =
      just (glb-left
        (glbᶜ-arrow-star-left glb₁
          (cast-Glbᶜ (sym eqL) (sym eqR) (sym eqL) glb₂)))
arrow-star-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ with aᴸ₁ ≟ImpAssm aᴸ₂ | aᴿ₁ ≟ImpAssm aᴿ₂
arrow-star-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = .aᴸ₁ ∷ Φᴸ₂} {Φᴿ = .aᴿ₁ ∷ Φᴿ₂} glb₂)
    | _ | _ | yes refl | yes refl =
      just (glb-left (glbᶜ-arrow-star-left-head-++ glb₁ glb₂))
arrow-star-search?
    (glb-left {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-left {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ | _ =
      just (glb-left (glbᶜ-arrow-star-left-++ glb₁ glb₂))
arrow-star-search?
    (glb-left {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-left {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | _ | _ = just (glb-left (glbᶜ-arrow-star-left-++ glb₁ glb₂))
arrow-star-search? _ _ = nothing

star-arrow-search? :
  ∀ {B₁ B₂} →
  GlbSearch⁺ ★ B₁ →
  GlbSearch⁺ ★ B₂ →
  Maybe (GlbSearch⁺ ★ (B₁ ⇒ B₂))
star-arrow-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    with Φᴸ₁ ≟ImpCtx Φᴸ₂ | Φᴿ₁ ≟ImpCtx Φᴿ₂
star-arrow-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | yes eqL | yes eqR =
      just (glb-right
        (glbᶜ-star-arrow-right glb₁
          (cast-Glbᶜ (sym eqL) (sym eqR) (sym eqR) glb₂)))
star-arrow-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ with aᴸ₁ ≟ImpAssm aᴸ₂ | aᴿ₁ ≟ImpAssm aᴿ₂
star-arrow-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = .aᴸ₁ ∷ Φᴸ₂} {Φᴿ = .aᴿ₁ ∷ Φᴿ₂} glb₂)
    | _ | _ | yes refl | yes refl =
      just (glb-right (glbᶜ-star-arrow-right-head-++ glb₁ glb₂))
star-arrow-search?
    (glb-right {Φᴸ = aᴸ₁ ∷ Φᴸ₁} {Φᴿ = aᴿ₁ ∷ Φᴿ₁} glb₁)
    (glb-right {Φᴸ = aᴸ₂ ∷ Φᴸ₂} {Φᴿ = aᴿ₂ ∷ Φᴿ₂} glb₂)
    | _ | _ | _ | _ =
      just (glb-right (glbᶜ-star-arrow-right-++ glb₁ glb₂))
star-arrow-search?
    (glb-right {Φᴸ = Φᴸ₁} {Φᴿ = Φᴿ₁} glb₁)
    (glb-right {Φᴸ = Φᴸ₂} {Φᴿ = Φᴿ₂} glb₂)
    | _ | _ = just (glb-right (glbᶜ-star-arrow-right-++ glb₁ glb₂))
star-arrow-search? {B₁ = B₁} {B₂ = B₂} result₁ result₂
    with closed-star-right? B₁ result₁ | closed-star-right? B₂ result₂
star-arrow-search? {B₁ = B₁} {B₂ = B₂} result₁ result₂
    | just glb₁ | just glb₂ =
      just (glb-right (glbᶜ-star-arrow-right glb₁ glb₂))
star-arrow-search? {B₁ = B₁} {B₂ = B₂} result₁ result₂ | _ | _ =
  nothing

lift-⊓ :
  ∀ (n m : ℕ) {A B} →
  GlbSearch⁺ A B →
  Maybe (Σ[ C ∈ Ty ] 0 ⊢ C ＝ add∀ n A ⊓ add∀ m B)
lift-⊓ n m result with lift-search⁺ n m result
lift-⊓ n m result | nothing = nothing
lift-⊓ n m result | just result′ = closed-search⇒⊓ (to-search result′)

{-# TERMINATING #-}
mutual
  glb-search? : (A B : Ty) → Maybe (GlbSearch⁺ A B)
  glb-search? A B with split-∀ A in sA | split-∀ B in sB
  glb-search? A B | n , A′ , n∀A | m , B′ , n∀B
      with core-glb? A′ B′ n∀A n∀B
  glb-search? A B | n , A′ , n∀A | m , B′ , n∀B | nothing = nothing
  glb-search? A B | n , A′ , n∀A | m , B′ , n∀B | just result
      with lift-search⁺ n m result
  glb-search? A B | n , A′ , n∀A | m , B′ , n∀B | just result
      | nothing = nothing
  glb-search? A B | n , A′ , n∀A | m , B′ , n∀B | just result
      | just lifted =
        just (cast-search⁺ʳ (split-add∀-from sB)
               (cast-search⁺ˡ (split-add∀-from sA) lifted))

  core-glb? :
    (A B : Ty) →
    Non∀ A →
    Non∀ B →
    Maybe (GlbSearch⁺ A B)
  core-glb? ★ (B₁ ⇒ B₂) nA nB
      with glb-search? ★ B₁ | glb-search? ★ B₂
  core-glb? ★ (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ with star-arrow-search? result₁ result₂
  core-glb? ★ (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ | just result = just result
  core-glb? ★ (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ | nothing = nothing
  core-glb? ★ (B₁ ⇒ B₂) nA nB | _ | _ = nothing
  core-glb? (A₁ ⇒ A₂) ★ nA nB
      with glb-search? A₁ ★ | glb-search? A₂ ★
  core-glb? (A₁ ⇒ A₂) ★ nA nB
      | just result₁ | just result₂ with arrow-star-search? result₁ result₂
  core-glb? (A₁ ⇒ A₂) ★ nA nB
      | just result₁ | just result₂ | just result = just result
  core-glb? (A₁ ⇒ A₂) ★ nA nB
      | just result₁ | just result₂ | nothing = nothing
  core-glb? (A₁ ⇒ A₂) ★ nA nB | _ | _ = nothing
  core-glb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
      with glb-search? A₁ B₁ | glb-search? A₂ B₂
  core-glb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ with arrow-search? result₁ result₂
  core-glb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ | just result = just result
  core-glb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB
      | just result₁ | just result₂ | nothing = nothing
  core-glb? (A₁ ⇒ A₂) (B₁ ⇒ B₂) nA nB | _ | _ = nothing
  core-glb? A B nA nB = core-glb-atomic? A B nA nB

glb? : (A B : Ty) → Maybe (Σ[ C ∈ Ty ] 0 ⊢ C ＝ A ⊓ B)
glb? A B with glb-search? A B
glb? A B | nothing = nothing
glb? A B | just result = closed-search⇒⊓ (to-search result)

glb?-consistent : (A B : Ty) → Maybe ([] ⊢ A ~ B)
glb?-consistent A B with glb? A B
glb?-consistent A B | nothing = nothing
glb?-consistent A B | just glb = just (glb-exists-consistent glb)

glb-∀base-star :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ (`∀ (‵ `ℕ)) ⊓ (`∀ ★)
glb-∀base-star =
  `∀ (‵ `ℕ) ,
  glbᶜ-closed⇒⊓
    (glbᶜ-lift-∀∀-open
      (glbᶜ-left-cons {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0}
        (glbᶜ-base-star {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}))
      (k∀ν left-∀∀-support)
      (kν∀ left-∀∀-support)
      (kνν left-∀∀-support))

glb-∀arrow-base-base :
  Σ[ C ∈ Ty ]
    0 ⊢ C ＝ (`∀ (‵ `ℕ ⇒ ★)) ⊓ (`∀ (★ ⇒ ‵ `ℕ))
glb-∀arrow-base-base =
  `∀ (‵ `ℕ ⇒ ‵ `ℕ) ,
  glbᶜ-closed⇒⊓
    (glbᶜ-lift-∀∀-open
      (glbᶜ-arrow-left-right-base-base
        (glbᶜ-left-cons {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0}
          (glbᶜ-base-star {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}))
        (glbᶜ-right-cons {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0}
          (glbᶜ-star-base {Φᴸ = []} {Φᴿ = []} {Φᴼ = []})))
      (k∀ν base-base-left-right-∀∀-support)
      (kν∀ base-base-left-right-∀∀-support)
      (kνν base-base-left-right-∀∀-support))

glb?-∀arrow-base-base :
  glb? (`∀ (‵ `ℕ ⇒ ★)) (`∀ (★ ⇒ ‵ `ℕ)) ≡
    just glb-∀arrow-base-base
glb?-∀arrow-base-base = refl

glb-∀arrow-base-base-right-left :
  Σ[ C ∈ Ty ]
    0 ⊢ C ＝ (`∀ (★ ⇒ ‵ `ℕ)) ⊓ (`∀ (‵ `ℕ ⇒ ★))
glb-∀arrow-base-base-right-left =
  `∀ (‵ `ℕ ⇒ ‵ `ℕ) ,
  glbᶜ-closed⇒⊓
    (glbᶜ-lift-∀∀-open
      (glbᶜ-arrow-right-left-base-base
        (glbᶜ-right-cons {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0}
          (glbᶜ-star-base {Φᴸ = []} {Φᴿ = []} {Φᴼ = []}))
        (glbᶜ-left-cons {aᴸ = 0 ˣ⊑ˣ 0} {aᴿ = 0 ˣ⊑ˣ 0}
          (glbᶜ-base-star {Φᴸ = []} {Φᴿ = []} {Φᴼ = []})))
      (k∀ν base-base-right-left-∀∀-support)
      (kν∀ base-base-right-left-∀∀-support)
      (kνν base-base-right-left-∀∀-support))

glb?-∀arrow-base-base-right-left :
  glb? (`∀ (★ ⇒ ‵ `ℕ)) (`∀ (‵ `ℕ ⇒ ★)) ≡
    just glb-∀arrow-base-base-right-left
glb?-∀arrow-base-base-right-left = refl

glb-∀arrow-var-star-star-base :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ (`∀ (＇ 0 ⇒ ★)) ⊓ (★ ⇒ ‵ `ℕ)
glb-∀arrow-var-star-star-base =
  `∀ (＇ 0 ⇒ ‵ `ℕ) ,
  glbᶜ-closed⇒⊓ (glbᶜ-lift-∀ν-arrow-var-base {κ = `ℕ})

glb?-∀arrow-var-star-star-base :
  glb? (`∀ (＇ 0 ⇒ ★)) (★ ⇒ ‵ `ℕ) ≡
    just glb-∀arrow-var-star-star-base
glb?-∀arrow-var-star-star-base = refl

glb-arrow-star-base-∀var-star :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ (★ ⇒ ‵ `ℕ) ⊓ (`∀ (＇ 0 ⇒ ★))
glb-arrow-star-base-∀var-star =
  `∀ (＇ 0 ⇒ ‵ `ℕ) ,
  glbᶜ-closed⇒⊓ (glbᶜ-lift-ν∀-arrow-base-var {κ = `ℕ})

glb?-arrow-star-base-∀var-star :
  glb? (★ ⇒ ‵ `ℕ) (`∀ (＇ 0 ⇒ ★)) ≡
    just glb-arrow-star-base-∀var-star
glb?-arrow-star-base-∀var-star = refl

glb-∀arrow-star-var-base-star :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ (`∀ (★ ⇒ ＇ 0)) ⊓ (‵ `ℕ ⇒ ★)
glb-∀arrow-star-var-base-star =
  `∀ (‵ `ℕ ⇒ ＇ 0) ,
  glbᶜ-closed⇒⊓ (glbᶜ-lift-∀ν-arrow-var-codomain {κ = `ℕ})

glb?-∀arrow-star-var-base-star :
  glb? (`∀ (★ ⇒ ＇ 0)) (‵ `ℕ ⇒ ★) ≡
    just glb-∀arrow-star-var-base-star
glb?-∀arrow-star-var-base-star = refl

glb-arrow-base-star-∀star-var :
  Σ[ C ∈ Ty ] 0 ⊢ C ＝ (‵ `ℕ ⇒ ★) ⊓ (`∀ (★ ⇒ ＇ 0))
glb-arrow-base-star-∀star-var =
  `∀ (‵ `ℕ ⇒ ＇ 0) ,
  glbᶜ-closed⇒⊓ (glbᶜ-lift-ν∀-arrow-var-codomain {κ = `ℕ})

glb?-arrow-base-star-∀star-var :
  glb? (‵ `ℕ ⇒ ★) (`∀ (★ ⇒ ＇ 0)) ≡
    just glb-arrow-base-star-∀star-var
glb?-arrow-base-star-∀star-var = refl

consistent-∀arrow-var-star-∀star-var :
  [] ⊢ `∀ (＇ 0 ⇒ ★) ~ `∀ (★ ⇒ ＇ 0)
consistent-∀arrow-var-star-∀star-var =
  A-~-∀ refl
    (∀-~-B refl
      (⇒-~-⇒
        (νX-~-★ (here refl))
        (★-~-νX (there (here refl)))))

consistent-∀arrow-star-var-∀var-star :
  [] ⊢ `∀ (★ ⇒ ＇ 0) ~ `∀ (＇ 0 ⇒ ★)
consistent-∀arrow-star-var-∀var-star =
  A-~-∀ refl
    (∀-~-B refl
      (⇒-~-⇒
        (★-~-νX (there (here refl)))
        (νX-~-★ (here refl))))

common-lower-∀arrow-var-star-∀star-var :
  CommonLower (`∀ (＇ 0 ⇒ ★)) (`∀ (★ ⇒ ＇ 0))
common-lower-∀arrow-var-star-∀star-var =
  consistent-common-lower consistent-∀arrow-var-star-∀star-var

common-lower-∀arrow-star-var-∀var-star :
  CommonLower (`∀ (★ ⇒ ＇ 0)) (`∀ (＇ 0 ⇒ ★))
common-lower-∀arrow-star-var-∀var-star =
  consistent-common-lower consistent-∀arrow-star-var-∀var-star
