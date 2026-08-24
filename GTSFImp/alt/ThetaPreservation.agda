module alt.ThetaPreservation where

-- File Charter:
--   * Records the remaining obstruction to one-step type preservation for the
--     Θ-indexed alternative calculus after `id-cancel` was made strict.
--   * The strict rule repairs the counterexample from commit c5ee0351: its
--     mismatched identity delimiters now form an adapter value rather than a
--     redex.  That historical instance remains below as a regression.
--   * The requested preservation statement is nevertheless false for a
--     different reason.  `β-reveal-⇒` moves its argument beneath a conceal
--     delimiter, whose typing rule requires a closed interior.  The reduction
--     rule asks only that the argument be a `Value`; a lambda value may capture
--     the ambient term context.  The checked instance below uses exactly such
--     a lambda, so its reduct cannot be typed.
--   * As pre-agreed, no partial preservation theorem, postulate, or hole is
--     introduced.  Repair requires a closedness premise on the function-
--     crossing β rules or a corresponding change to crossing interiors.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

------------------------------------------------------------------------
-- Historical strict-id regression
------------------------------------------------------------------------

bad-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ ,typ[ zero ] ,typ[ zero ]

bad-body-Ψ : TyEnv (suc (suc zero)) (suc (suc zero))
bad-body-Ψ =
  ∅ ,:= ‵ `ℕ ,:= ‵ `ℕ ,typ[ zero ] ,typ[ suc zero ]

bad-V : Term (suc (suc zero)) (suc (suc zero))
bad-V = ($ (κℕ 7)) ↓[ zero ≔ zero ] seal

bad-V-⊢ : bad-body-Ψ ∣ [] ⊢ bad-V ⦂ ＇ zero
bad-V-⊢ = ⊢conceal (skip-typ Z) ⊢seal (⊢$ (κℕ 7))

bad-inner : Term (suc (suc zero)) (suc (suc (suc zero)))
bad-inner = bad-V ↓[ zero ≔ zero ] id↓

bad-inner-⊢ :
  bad-Ψ ,typ[ suc (suc zero) ] ∣ [] ⊢ bad-inner ⦂ ＇ suc zero
bad-inner-⊢ =
  ⊢conceal (skip-typ (skip-typ Z)) (⊢id↓ (＇ suc zero)) bad-V-⊢

bad-redex : Term (suc (suc zero)) (suc (suc zero))
bad-redex = bad-inner ↑[ suc (suc zero) ≔ suc zero ] id↑

bad-redex-⊢ : bad-Ψ ∣ [] ⊢ bad-redex ⦂ ＇ suc zero
bad-redex-⊢ =
  ⊢reveal (skip-typ (skip-typ (S Z)))
    (⊢id↑ (＇ suc zero)) bad-inner-⊢

bad-V-canonical : CanonicalInterior bad-V
bad-V-canonical = sealed ($ (κℕ 7)) zero zero

bad-inner-value : Value bad-inner
bad-inner-value =
  canonical-value bad-V-canonical
    ↓[ zero ≔ zero ] delimiter bad-V-canonical

bad-node-pair-mismatch :
  ¬ ((Fin.suc {n = 2} (Fin.suc {n = 1} (Fin.zero {n = 0}))
      ≡ Fin.zero {n = 2})
    × (Fin.suc {n = 1} (Fin.zero {n = 0}) ≡ Fin.zero {n = 1}))
bad-node-pair-mismatch (() , anchor-eq)

-- This was the preservation-refuting redex in commit c5ee0351.  With strict
-- `id-cancel`, the unequal (slot, anchor) pairs make it an adapter value.
bad-redex-value : Value bad-redex
bad-redex-value =
  bad-inner-value ↑[ suc (suc zero) ≔ suc zero ]
    adapter bad-V-canonical bad-node-pair-mismatch

constant-no-step : ∀ {Θ Δ} {Φ : TyEnv Θ Δ} {κ M′}
  → Φ ⊢ $ κ —→ M′
  → ⊥
constant-no-step ()

bad-V-no-step : ∀ {Φ : TyEnv 2 2} {M′}
  → Φ ⊢ bad-V —→ M′
  → ⊥
bad-V-no-step (ξ-conceal step) = constant-no-step step

bad-inner-no-step : ∀ {Φ : TyEnv 2 3} {M′}
  → Φ ⊢ bad-inner —→ M′
  → ⊥
bad-inner-no-step (ξ-conceal step) = bad-V-no-step step

bad-redex-no-step : ∀ {M′}
  → bad-Ψ ⊢ bad-redex —→ M′
  → ⊥
bad-redex-no-step (ξ-reveal step) = bad-inner-no-step step

------------------------------------------------------------------------
-- Remaining `β-reveal-⇒` obstruction
------------------------------------------------------------------------

open-R : Ty zero
open-R = ‵ `ℕ ⇒ ‵ `ℕ

open-Ψ : TyEnv (suc zero) zero
open-Ψ = ∅ ,:= open-R

open-Γ : TermCtx zero
open-Γ = ‵ `ℕ ∷ []

open-V : Term (suc zero) (suc zero)
open-V = ƛ ＇ zero ˙ $ (κℕ 0)

open-V-⊢ :
  open-Ψ ,typ[ zero ] ∣ [] ⊢ open-V ⦂ ＇ zero ⇒ ‵ `ℕ
open-V-⊢ = ⊢ƛ (⊢$ (κℕ 0))

open-V-value : Value open-V
open-V-value = ƛ ＇ zero ˙ $ (κℕ 0)

open-W : Term (suc zero) zero
open-W = ƛ ‵ `ℕ ˙ ` suc zero

open-W-⊢ : open-Ψ ∣ open-Γ ⊢ open-W ⦂ open-R
open-W-⊢ = ⊢ƛ (⊢` (S Z))

open-W-value : Value open-W
open-W-value = ƛ ‵ `ℕ ˙ ` suc zero

open-function : Term (suc zero) zero
open-function = open-V ↑[ zero ≔ zero ] (seal ↦↑ id↑)

open-function-⊢ :
  open-Ψ ∣ open-Γ ⊢ open-function ⦂ open-R ⇒ ‵ `ℕ
open-function-⊢ =
  ⊢reveal Z (⊢↑-⇒ ⊢seal (⊢id↑ (‵ `ℕ))) open-V-⊢

open-redex : Term (suc zero) zero
open-redex = open-function · open-W

open-redex-⊢ : open-Ψ ∣ open-Γ ⊢ open-redex ⦂ ‵ `ℕ
open-redex-⊢ = ⊢· open-function-⊢ open-W-⊢

open-contractum : Term (suc zero) zero
open-contractum =
  (open-V · (open-W ↓[ zero ≔ zero ] seal))
    ↑[ zero ≔ zero ] id↑

open-step : open-Ψ ⊢ open-redex —→ open-contractum
open-step = β-reveal-⇒ open-V-value open-W-value

open-W-closed-impossible : ∀ {Φ : TyEnv (suc zero) zero} {A}
  → Φ ∣ [] ⊢ open-W ⦂ A
  → ⊥
open-W-closed-impossible (⊢ƛ (⊢` (S ())))

open-contractum-untypable :
  open-Ψ ∣ open-Γ ⊢ open-contractum ⦂ ‵ `ℕ
  → ⊥
open-contractum-untypable
    (⊢reveal α∈ c⊢
      (⊢· V⊢ (⊢conceal β∈ d⊢ W⊢))) =
  open-W-closed-impossible W⊢

preserve-impossible :
  (∀ {Θ Δ} {Ψ : TyEnv Θ Δ} {Γ} {M M′ A}
    → Ψ ∣ Γ ⊢ M ⦂ A
    → Ψ ⊢ M —→ M′
    → Ψ ∣ Γ ⊢ M′ ⦂ A)
  → ⊥
preserve-impossible preserve =
  open-contractum-untypable (preserve open-redex-⊢ open-step)
