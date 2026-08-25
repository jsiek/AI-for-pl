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
  skip-end (skip-nu-binding found-begin)
    (S (skip-begin Z)) (S (skip-begin Z))
    (resolve-wkᵗ zero (‵ `ℕ) (‵ `ℕ))

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
  skip-end (skip-nu-binding found-begin)
    (S (skip-begin Z)) Z (resolveSub-here zero (‵ `ℕ))

-- A live begin weakens an outer representation verbatim.
verbatim-through-live-begin :
  (∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ] ∋rep zero
    ≔ wkᵗ zero (‵ `ℕ)
verbatim-through-live-begin = skip-begin Z

end-after-live-begin :
  (((∅ ,:= ‵ `ℕ ,:= ‵ `𝔹) ,begin[ zero ≔ zero ])
      ,begin[ suc zero ≔ suc zero ]) ,end[ zero ]
    ∋rep suc zero ≔ ‵ `ℕ
end-after-live-begin =
  skip-end (skip-begin found-begin)
    (skip-begin (skip-begin Z))
    (skip-begin (skip-begin (S Z)))
    (resolve-wkᵗ zero (‵ `𝔹) (‵ `ℕ))

------------------------------------------------------------------------
-- The former β-Λ allocation obstruction is now a positive instance
------------------------------------------------------------------------

βΛ-Ψ : TyEnv 1 0
βΛ-Ψ = ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]) ,end[ zero ]

βΛ-ended-lookup : βΛ-Ψ ∋rep zero ≔ ‵ `ℕ
βΛ-ended-lookup =
  skip-end found-begin (skip-begin Z) (skip-begin Z)
    (resolve-wkᵗ zero (‵ `ℕ) (‵ `ℕ))

βΛ-body : Term 1 1
βΛ-body = (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] `∀↑ id↑

βΛ-body-value : Value βΛ-body
βΛ-body-value =
  result-val (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] all

βΛ-body-⊢ : βΛ-Ψ ,typ ∣ [] ⊢ βΛ-body ⦂ `∀ (‵ `ℕ)
βΛ-body-⊢ =
  ⊢reveal (skip-typ βΛ-ended-lookup)
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
  ⊢ν (⊢reveal Z (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
    (⊢allocate-lexical βΛ-body-⊢))

βΛ-positive-preservation :
  (βΛ-Ψ ∣ [] ⊢ βΛ-redex ⦂ `∀ (‵ `ℕ))
  × ((βΛ-Ψ ⊢ βΛ-redex —→ βΛ-contractum)
    × (βΛ-Ψ ∣ [] ⊢ βΛ-contractum ⦂ `∀ (‵ `ℕ)))
βΛ-positive-preservation =
  βΛ-redex-⊢ , βΛ-step , βΛ-contractum-⊢
