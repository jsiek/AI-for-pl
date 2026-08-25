module alt.ThetaRegression where

-- File Charter:
--   * Checks the counterexample that previously blocked literal type weakening,
--     term substitution, and preservation of the right-application float.
--   * The ambient telescope ends in an anchor whose representation mentions
--     the slot concealed by `sealed-seven`; crossing its end marker resolves
--     the older natural-number representation in the lookup result.
--   * Exhibits the conceal typing derivation, a chained ν-headed result, its
--     `float-·₂` step, and concrete typings for both sides of that step.

open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

Ψ₂ : TyEnv 2 1
Ψ₂ = ∅ ,:= ‵ `ℕ ,begin[ zero ≔ zero ] ,:= ＇ zero

Ψ₂-ended-old-lookup : Ψ₂ ,end[ zero ] ∋rep suc zero ≔ ‵ `ℕ
Ψ₂-ended-old-lookup =
  ∋rep-of
    (skip-end (skip-nu-binding found-begin)
      (S (skip-begin Z)))
    ⇓-base

sealed-seven : Term 2 1
sealed-seven = ($ (κℕ 7)) ↓[ zero ≔ suc zero ] seal

sealed-seven-⊢ : Ψ₂ ∣ [] ⊢ sealed-seven ⦂ ＇ zero
sealed-seven-⊢ =
  ⊢conceal (skip-nu-binding found-begin) Ψ₂-ended-old-lookup
    ⊢seal (⊢$ (κℕ 7))

g : Term 2 1
g = ƛ ＇ zero ˙ ` zero

g-⊢ : Ψ₂ ∣ [] ⊢ g ⦂ ＇ zero ⇒ ＇ zero
g-⊢ = ⊢ƛ (⊢` Z)

g-value : Value g
g-value = ƛ ＇ zero ˙ ` zero

a : Term 2 1
a = ν[ ‵ `ℕ ] (ν[ ‵ `ℕ ] shiftᶿ (shiftᶿ sealed-seven))

shifted-seven-⊢ :
  Ψ₂ ,:= ‵ `ℕ ,:= ‵ `ℕ ∣ []
    ⊢ shiftᶿ (shiftᶿ sealed-seven) ⦂ ＇ zero
shifted-seven-⊢ = ⊢shiftᶿ (⊢shiftᶿ sealed-seven-⊢)

a-body-⊢ :
  Ψ₂ ,:= ‵ `ℕ ∣ []
    ⊢ ν[ ‵ `ℕ ] shiftᶿ (shiftᶿ sealed-seven) ⦂ ＇ zero
a-body-⊢ = ⊢ν shifted-seven-⊢

a-⊢ : Ψ₂ ∣ [] ⊢ a ⦂ ＇ zero
a-⊢ = ⊢ν a-body-⊢

shifted-seven-value : Value (shiftᶿ (shiftᶿ sealed-seven))
shifted-seven-value =
  result-val ($ (κℕ 7))
    ↓[ zero ≔ suc (suc (suc zero)) ] sealᵥ

a-result : Result a
a-result = result-ν (result-ν (result-val shifted-seven-value))

floated : Term 2 1
floated =
  ν[ ‵ `ℕ ]
    (shiftᶿ g · (ν[ ‵ `ℕ ] shiftᶿ (shiftᶿ sealed-seven)))

float-step : Ψ₂ ⊢ g · a —→ floated
float-step = float-·₂ g-value a-result

before-float-⊢ : Ψ₂ ∣ [] ⊢ g · a ⦂ ＇ zero
before-float-⊢ = ⊢· g-⊢ a-⊢

after-float-⊢ : Ψ₂ ∣ [] ⊢ floated ⦂ ＇ zero
after-float-⊢ =
  ⊢ν (⊢· (⊢shiftᶿ g-⊢) a-body-⊢)

float-preservation-instance :
  Ψ₂ ∣ [] ⊢ g · a ⦂ ＇ zero
  × Ψ₂ ∣ [] ⊢ floated ⦂ ＇ zero
float-preservation-instance = before-float-⊢ , after-float-⊢

------------------------------------------------------------------------
-- Lazy begin/end lookup regressions
------------------------------------------------------------------------

-- Ending the recorded slot resolves the later anchor's slot-dependent
-- representation in the lookup result; the telescope itself is unchanged.
resolve-through-end : Ψ₂ ,end[ zero ] ∋rep zero ≔ ‵ `ℕ
resolve-through-end =
  ∋rep-of
    (skip-end (skip-nu-binding found-begin) Z)
    (⇓-ref Ψ₂-ended-old-lookup)

-- A live begin weakens an outer representation verbatim.
verbatim-through-live-begin :
  (∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ] ∋rep zero
    ≔ wkᵗ zero (‵ `ℕ)
verbatim-through-live-begin = ∋rep-here-begin

end-after-live-begin :
  (((∅ ,:= ‵ `ℕ ,:= ‵ `𝔹) ,begin[ zero ≔ zero ])
      ,begin[ suc zero ≔ suc zero ]) ,end[ zero ]
    ∋rep suc zero ≔ ‵ `ℕ
end-after-live-begin =
  ∋rep-of
    (skip-end (skip-begin found-begin)
      (skip-begin (skip-begin (S Z))))
    ⇓-base

-- The telescope from commit 0190acb9 now re-enters the just-ended anchor
-- abstractly.  The end creates `ref (suc zero)` and the adjacent begin turns
-- it back into the new slot.
adjacent-reentry :
    (reenter-counterexample-Ψ ,end[ zero ]
      ,begin[ zero ≔ suc zero ]) ∋rep zero ≔ ＇ zero
adjacent-reentry = reenter-counterexample-reentered

nonadjacent-reentry-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
nonadjacent-reentry-Ψ =
  (((((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]) ,:= ＇ zero)
    ,end[ zero ]) ,typ) ,begin[ zero ≔ suc zero ]

-- A lexical entry between the end and its later begin leaves refs fixed;
-- the later begin still re-aliases the ended anchor to its new abstract slot.
nonadjacent-reentry :
    nonadjacent-reentry-Ψ ∋rep zero ≔ ＇ zero
nonadjacent-reentry =
  ∋rep-of
    (skip-begin
      (skip-typ
        (skip-end (skip-nu-binding found-begin) Z)))
    ⇓-var

------------------------------------------------------------------------
-- The former β-Λ allocation obstruction is now a positive instance
------------------------------------------------------------------------

βΛ-Ψ : TyEnv 1 0
βΛ-Ψ = ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]) ,end[ zero ]

βΛ-ended-lookup : βΛ-Ψ ∋rep zero ≔ ‵ `ℕ
βΛ-ended-lookup =
  ∋rep-of (skip-end found-begin (skip-begin Z)) ⇓-base

βΛ-body : Term 1 1
βΛ-body = (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] `∀↑ id↑

βΛ-body-value : Value βΛ-body
βΛ-body-value =
  result-val (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] all

βΛ-body-⊢ : βΛ-Ψ ,typ ∣ [] ⊢ βΛ-body ⦂ `∀ (‵ `ℕ)
βΛ-body-⊢ =
  ⊢reveal (∋rep-typ βΛ-ended-lookup)
    (⊢↑-∀ (⊢id↑ (‵ `ℕ))) (⊢Λ (⊢$ (κℕ 7)))

βΛ-redex : Term 1 0
βΛ-redex = (Λ βΛ-body) ⦂∀ `∀ (‵ `ℕ) [ ‵ `ℕ ]

βΛ-contractum : Term 1 0
βΛ-contractum =
  ν[ ‵ `ℕ ]
    (shiftᶿ βΛ-body ↑[ zero ≔ zero ] `∀↑ id↑)

βΛ-redex-⊢ : βΛ-Ψ ∣ [] ⊢ βΛ-redex ⦂ `∀ (‵ `ℕ)
βΛ-redex-⊢ = ⊢⦂∀ (⊢Λ βΛ-body-⊢)

βΛ-step : βΛ-Ψ ⊢ βΛ-redex —→ βΛ-contractum
βΛ-step = β-Λ βΛ-body-value

βΛ-contractum-⊢ :
  βΛ-Ψ ∣ [] ⊢ βΛ-contractum ⦂ `∀ (‵ `ℕ)
βΛ-contractum-⊢ =
  ⊢ν (⊢reveal ∋rep-here (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
    (⊢allocate-lexical βΛ-body-⊢))

βΛ-positive-preservation :
  (βΛ-Ψ ∣ [] ⊢ βΛ-redex ⦂ `∀ (‵ `ℕ))
  × ((βΛ-Ψ ⊢ βΛ-redex —→ βΛ-contractum)
    × (βΛ-Ψ ∣ [] ⊢ βΛ-contractum ⦂ `∀ (‵ `ℕ)))
βΛ-positive-preservation =
  βΛ-redex-⊢ , βΛ-step , βΛ-contractum-⊢
