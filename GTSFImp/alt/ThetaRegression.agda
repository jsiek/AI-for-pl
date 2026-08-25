module alt.ThetaRegression where

-- File Charter:
--   * Checks the counterexample that previously blocked literal type weakening,
--     term substitution, and preservation of the right-application float.
--   * The ambient telescope ends in an anchor whose representation mentions
--     the slot concealed by `sealed-seven`; resolving deletion substitutes
--     the older natural-number representation into that later anchor.
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

sealed-seven : Term 2 1
sealed-seven = ($ (κℕ 7)) ↓[ zero ≔ suc zero ] seal

sealed-seven-⊢ : Ψ₂ ∣ [] ⊢ sealed-seven ⦂ ＇ zero
sealed-seven-⊢ =
  ⊢conceal (skip-nu-binding here-typ) (S Z)
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
