module alt.ThetaRegression where

-- File Charter:
--   * Exercises anchor-directed representation lookup through end markers,
--     re-entry, lexical drift, and freshly allocated crossings.
--   * Retains the ν-headed application-float regression that originally
--     exposed the missing telescope transports.
--   * Checks the former β-Λ obstruction as a positive preservation instance.

open import Data.Fin using (zero; suc)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst

empty-fresh : ∀ {Θ} {a : TyVar Θ} → a ∉ᵛ Vec.[]
empty-fresh ()

nothing-fresh : ∀ {Θ} {a : TyVar Θ}
  → a ∉ᵛ (nothing Vec.∷ Vec.[])
nothing-fresh zero ()

one-zero-tyVar : Vec.Vec (Maybe (TyVar 2)) 1
one-zero-tyVar = just zero Vec.∷ Vec.[]

other-fresh : suc zero ∉ᵛ one-zero-tyVar
other-fresh zero ()

------------------------------------------------------------------------
-- The original application-float regression
------------------------------------------------------------------------

Ψ₂-σ : Vec.Vec (Maybe (TyVar 2)) 1
Ψ₂-σ = just (suc zero) Vec.∷ Vec.[]

Ψ₂ : TyEnv 2 1 Ψ₂-σ
Ψ₂ =
  ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩) ,:= ＇ zero

Ψ₂-ended-old-lookup :
  rep? (Ψ₂ ,end[ zero ]) (suc zero) ≡ just (‵ `ℕ)
Ψ₂-ended-old-lookup = refl

sealed-seven : Term 2 1
sealed-seven = ($ (κℕ 7)) ↓[ zero ≔ suc zero ] seal

sealed-seven-⊢ : Ψ₂ ∣ [] ⊢ sealed-seven ⦂ ＇ zero
sealed-seven-⊢ =
  ⊢conceal refl Ψ₂-ended-old-lookup ⊢seal (⊢$ (κℕ 7))

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
after-float-⊢ = ⊢ν (⊢· (⊢shiftᶿ g-⊢) a-body-⊢)

float-preservation-instance :
  Ψ₂ ∣ [] ⊢ g · a ⦂ ＇ zero
  × Ψ₂ ∣ [] ⊢ floated ⦂ ＇ zero
float-preservation-instance = before-float-⊢ , after-float-⊢

------------------------------------------------------------------------
-- Anchor-directed lookup regressions
------------------------------------------------------------------------

-- The old anchor is dead after the end, so its representation resolves.
resolve-through-end : rep? (Ψ₂ ,end[ zero ]) zero ≡ just (‵ `ℕ)
resolve-through-end = refl

-- A representation is read verbatim at its birth scope through a live begin.
verbatim-through-live-begin :
  rep? ((∅ ,:= ‵ `ℕ)
    ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩) zero ≡ just (‵ `ℕ)
verbatim-through-live-begin = refl

two-crossings : TyEnv 2 2
  (just zero Vec.∷ just (suc zero) Vec.∷ Vec.[])
two-crossings =
  ((∅ ,:= ‵ `ℕ ,:= ‵ `𝔹)
    ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩)
    ,begin[ suc zero ≔ suc zero ]⟨ other-fresh ⟩

-- Ending one crossing leaves the unrelated live anchor available.
end-after-live-begin :
  rep? (two-crossings ,end[ zero ]) (suc zero) ≡ just (‵ `ℕ)
end-after-live-begin = refl

adjacent-reentry-Ψ : TyEnv 2 1 Ψ₂-σ
adjacent-reentry-Ψ =
  (Ψ₂ ,end[ zero ])
    ,begin[ zero ≔ suc zero ]⟨ empty-fresh ⟩

-- Commit 0190acb9's adjacent re-entry now computes the same abstract payload.
adjacent-reentry : rep? adjacent-reentry-Ψ zero ≡ just (＇ zero)
adjacent-reentry = refl

nonadjacent-reentry-σ : Vec.Vec (Maybe (TyVar 2)) 2
nonadjacent-reentry-σ = just (suc zero) Vec.∷ nothing Vec.∷ Vec.[]

nonadjacent-reentry-Ψ : TyEnv 2 2 nonadjacent-reentry-σ
nonadjacent-reentry-Ψ =
  ((Ψ₂ ,end[ zero ]) ,typ)
    ,begin[ zero ≔ suc zero ]⟨ nothing-fresh ⟩

-- A lexical insertion between end and re-entry changes only positions.
nonadjacent-reentry :
  rep? nonadjacent-reentry-Ψ zero ≡ just (＇ zero)
nonadjacent-reentry = refl

------------------------------------------------------------------------
-- The former β-Λ allocation obstruction is now a positive instance
------------------------------------------------------------------------

βΛ-Ψ : TyEnv 1 0 Vec.[]
βΛ-Ψ =
  ((∅ ,:= ‵ `ℕ) ,begin[ zero ≔ zero ]⟨ empty-fresh ⟩) ,end[ zero ]

βΛ-ended-lookup : rep? βΛ-Ψ zero ≡ just (‵ `ℕ)
βΛ-ended-lookup = refl

βΛ-body : Term 1 1
βΛ-body = (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] `∀↑ id↑

βΛ-body-value : Value βΛ-body
βΛ-body-value =
  result-val (Λ ($ (κℕ 7))) ↑[ zero ≔ zero ] all

βΛ-body-⊢ : βΛ-Ψ ,typ ∣ [] ⊢ βΛ-body ⦂ `∀ (‵ `ℕ)
βΛ-body-⊢ =
  ⊢reveal {fresh = nothing-fresh}
    (rep?-typ {Θ = 1} {Ψ = βΛ-Ψ} {α = zero}
      {A = ‵ `ℕ} βΛ-ended-lookup)
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
  ⊢ν (⊢reveal (rep?-here {Θ = 1} {Ψ = βΛ-Ψ} {A = ‵ `ℕ})
    (⊢↑-∀ (⊢id↑ (‵ `ℕ)))
    (⊢allocate-lexical βΛ-body-⊢))

βΛ-positive-preservation :
  (βΛ-Ψ ∣ [] ⊢ βΛ-redex ⦂ `∀ (‵ `ℕ))
  × ((βΛ-Ψ ⊢ βΛ-redex —→ βΛ-contractum)
    × (βΛ-Ψ ∣ [] ⊢ βΛ-contractum ⦂ `∀ (‵ `ℕ)))
βΛ-positive-preservation =
  βΛ-redex-⊢ , βΛ-step , βΛ-contractum-⊢
