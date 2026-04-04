module intrinsic.Reduction where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import intrinsic.Types
open import intrinsic.Ctx
open import intrinsic.Terms

infix 2 _—→_

data Value : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Set where

  V-zero : ∀ {Δ} {Γ : Ctx Δ}
      ---------------------------
    → Value (`zero {Γ = Γ})

  V-suc : ∀ {Δ} {Γ : Ctx Δ} {V : Δ ; Γ ⊢ `Nat}
    → Value V
      ---------------------------
    → Value (`suc V)

  V-true : ∀ {Δ} {Γ : Ctx Δ}
      ---------------------------
    → Value (`true {Γ = Γ})

  V-false : ∀ {Δ} {Γ : Ctx Δ}
      ----------------------------
    → Value (`false {Γ = Γ})

  V-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B}
      ------------------------------------
    → Value (ƛ A ˙ N)

  V-Λ : ∀ {Δ Γ A} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ------------------------------------
    → Value (Λ N)


data _—→_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ; Γ ⊢ A → Set where

  ξ-suc : ∀ {Δ Γ} {M M′ : Δ ; Γ ⊢ `Nat}
    →     M —→ M′
      ---------------------
    → `suc M —→ `suc M′

  ξ-case-nat : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
    →     L —→ L′
      -----------------------------------------------
    → `case-nat L M N —→ `case-nat L′ M N

  ξ-if : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
    →     L —→ L′
      -------------------------------------------------
    → `if_then_else L M N —→ `if_then_else L′ M N

  ξ-·₁ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A ⇒ B} {M}
    →     L —→ L′
      ---------------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A ⇒ B} {M M′}
    →     Value V
    →     M —→ M′
      ------------------------
    → V · M —→ V · M′

  -- | New congruence rule for System F
  ξ-∙ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
    →     M —→ M′
      ---------------------------------------
    → M ∙ B —→ M′ ∙ B

  β-ƛ : ∀ {Δ Γ A B} {N : Δ ; Γ , A ⊢ B} {W}
    →          Value W
      ------------------------------
    → (ƛ A ˙ N) · W —→ N [ W ]

  β-zero :  ∀ {Δ Γ A} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
      ------------------------------------------
    → `case-nat `zero M N —→ M

  β-suc : ∀ {Δ Γ A} {V : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
    → Value V
      ------------------------------------------------
    → `case-nat (`suc V) M N —→ N [ V ]

  β-true : ∀ {Δ Γ A} {M N : Δ ; Γ ⊢ A}
      ------------------------------------------
    → `if_then_else `true M N —→ M

  β-false : ∀ {Δ Γ A} {M N : Δ ; Γ ⊢ A}
      -------------------------------------------
    → `if_then_else `false M N —→ N

  -- | New beta rule for System F
  β-Λ : ∀ {Δ Γ A B} {N : Δ ,α ; ⇑ᶜ Γ ⊢ A}
      ---------------------------------------
    → (Λ N) ∙ B —→ N [ B ]ᵀ

------------------
-- | Progress | --
------------------

data Progress {A} (M : ∅ ; ∅ ⊢ A) : Set where

  step : ∀ {N : ∅ ; ∅ ⊢ A}
    → M —→ N
      ------------
    → Progress M

  done :
      Value M
      ----------
    → Progress M

progress : ∀ {A} → (M : ∅ ; ∅ ⊢ A) → Progress M
progress `zero = done V-zero
progress `true = done V-true
progress `false = done V-false
progress (`suc M) = case progress M of λ where
  (step M→M′) → step (ξ-suc M→M′)
  (done vM) → done (V-suc vM)
progress (`case-nat L M N) = case progress L of λ where
  (step L→L′) → step (ξ-case-nat L→L′)
  (done V-zero) → step β-zero
  (done (V-suc vL)) → step (β-suc vL)
progress (`if_then_else L M N) = case progress L of λ where
  (step L→L′) → step (ξ-if L→L′)
  (done V-true) → step β-true
  (done V-false) → step β-false
progress (ƛ A ˙ N) = done V-ƛ
progress (Λ N) = done V-Λ
progress (L · M) = case progress L of λ where
  (step L→L′) → step (ξ-·₁ L→L′)
  (done vL) → case progress M of λ where
    (step M→M′) → step (ξ-·₂ vL M→M′)
    (done vM) → case vL of λ where
      V-ƛ → step (β-ƛ vM)
progress (M ∙ B) = case progress M of λ where
  (step M→M′) → step (ξ-∙ M→M′)
  (done vM) → case vM of λ where
    V-Λ → step β-Λ

infix 2 _—↠_

data _—↠_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} → Δ ; Γ ⊢ A → Δ ; Γ ⊢ A → Set where
  _∎ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ} (M : Δ ; Γ ⊢ A) → M —↠ M

  _—→⟨_⟩_ : ∀ {Δ} {Γ : Ctx Δ} {A : Type Δ}
    (L : Δ ; Γ ⊢ A) {M N : Δ ; Γ ⊢ A}
    → L —→ M
    → M —↠ N
    → L —↠ N

↠-trans : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —↠ M
  → M —↠ N
  → L —↠ N
↠-trans (L ∎) M—↠N = M—↠N
↠-trans (L —→⟨ L—→M ⟩ Lrest) M—↠N = L —→⟨ L—→M ⟩ (↠-trans Lrest M—↠N)

step-eq-↠ : ∀ {Δ Γ A} {L M N : Δ ; Γ ⊢ A}
  → L —→ M
  → M ≡ N
  → L —↠ N
step-eq-↠ {M = M} L—→M refl = _ —→⟨ L—→M ⟩ (M ∎)

suc-↠ : ∀ {Δ Γ} {M M′ : Δ ; Γ ⊢ `Nat}
  → M —↠ M′
  → `suc M —↠ `suc M′
suc-↠ (M ∎) = (`suc M) ∎
suc-↠ (M —→⟨ M—→M′ ⟩ M′—↠M″) =
  (`suc M) —→⟨ ξ-suc M—→M′ ⟩ suc-↠ M′—↠M″

case-nat-↠ : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Nat} {M : Δ ; Γ ⊢ A} {N : Δ ; Γ , `Nat ⊢ A}
  → L —↠ L′
  → `case-nat L M N —↠ `case-nat L′ M N
case-nat-↠ {M = M} {N = N} (L ∎) = `case-nat L M N ∎
case-nat-↠ {M = M} {N = N} (L —→⟨ L—→L′ ⟩ L′—↠L″) =
  `case-nat L M N —→⟨ ξ-case-nat L—→L′ ⟩ case-nat-↠ {M = M} {N = N} L′—↠L″

if-↠ : ∀ {Δ Γ A} {L L′ : Δ ; Γ ⊢ `Bool} {M N : Δ ; Γ ⊢ A}
  → L —↠ L′
  → `if_then_else L M N —↠ `if_then_else L′ M N
if-↠ {M = M} {N = N} (L ∎) = `if_then_else L M N ∎
if-↠ {M = M} {N = N} (L —→⟨ L—→L′ ⟩ L′—↠L″) =
  `if_then_else L M N —→⟨ ξ-if L—→L′ ⟩ if-↠ {M = M} {N = N} L′—↠L″

·₁-↠ : ∀ {Δ Γ A B} {L L′ : Δ ; Γ ⊢ A ⇒ B} {M}
  → L —↠ L′
  → L · M —↠ L′ · M
·₁-↠ {M = M} (L ∎) = (L · M) ∎
·₁-↠ {M = M} (L —→⟨ L—→L′ ⟩ L′—↠L″) = (L · M) —→⟨ ξ-·₁ L—→L′ ⟩ ·₁-↠ {M = M} L′—↠L″

·₂-↠ : ∀ {Δ Γ A B} {V : Δ ; Γ ⊢ A ⇒ B} {M M′}
  → Value V
  → M —↠ M′
  → V · M —↠ V · M′
·₂-↠ {V = V} vV (M ∎) = (V · M) ∎
·₂-↠ {V = V} vV (M —→⟨ M—→M′ ⟩ M′—↠M″) = (V · M) —→⟨ ξ-·₂ vV M—→M′ ⟩ ·₂-↠ vV M′—↠M″

∙-↠ : ∀ {Δ Γ A B} {M M′ : Δ ; Γ ⊢ `∀ A}
  → M —↠ M′
  → M ∙ B —↠ M′ ∙ B
∙-↠ {B = B} (M ∎) = (M ∙ B) ∎
∙-↠ {B = B} (M —→⟨ M—→M′ ⟩ M′—↠M″) = (M ∙ B) —→⟨ ξ-∙ M—→M′ ⟩ ∙-↠ {B = B} M′—↠M″
