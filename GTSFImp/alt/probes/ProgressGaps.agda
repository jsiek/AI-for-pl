module alt.probes.ProgressGaps where

-- File Charter:
--   * Records the missing adapter-region/unseal merge needed before function
--     application: a ν-stranded seal/unseal value at function type is stuck.
--   * Rechecks the gap against persistent ν results using `value-no-step`.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import Primitives
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-here)
open import alt.ThetaProgress using
  (CanonicalFun; Progress; step; done; failed)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕ⇒ℕ

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

crossedEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossedEnv = baseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

regionEnv : TyEnv 2 1 (just (suc zero) Vec.∷ Vec.[])
regionEnv = crossedEnv ,:= ℕᵗ

identity : ∀ {Θ} → Term Θ zero
identity = ƛ ℕᵗ ˙ ` zero

sealedTerm : Term 2 1
sealedTerm = identity ↓[ zero ≔ suc zero ] seal

stranded : Term 1 1
stranded = ν[ ℕᵗ ] sealedTerm

stuckFun : Term 1 zero
stuckFun = stranded ↑[ zero ≔ zero ] unseal

stuck : Term 1 zero
stuck = stuckFun · $ (κℕ zero)

identity-typed : regionEnv ,end[ zero ] ∣ [] ⊢ identity ⦂ ℕ⇒ℕ
identity-typed = ⊢ƛ (⊢` Z)

sealed-typed : regionEnv ∣ [] ⊢ sealedTerm ⦂ ＇ zero
sealed-typed = ⊢conceal refl refl ⊢seal identity-typed

stranded-typed : crossedEnv ∣ [] ⊢ stranded ⦂ ＇ zero
stranded-typed = ⊢ν sealed-typed

stuckFun-typed : baseEnv ∣ [] ⊢ stuckFun ⦂ ℕ⇒ℕ
stuckFun-typed = ⊢reveal {fresh = no-live-anchor}
  (rep?-here {Ψ = baseEnv}) ⊢unseal stranded-typed

stuck-typed : baseEnv ∣ [] ⊢ stuck ⦂ ℕᵗ
stuck-typed = ⊢· stuckFun-typed (⊢$ (κℕ zero))

identity-value : Value (identity {Θ = 2})
identity-value = ƛ ℕᵗ ˙ ` zero

sealed-value : Value sealedTerm
sealed-value = result-val identity-value ↓[ zero ≔ suc zero ] sealᵥ

sealed-result : Result sealedTerm
sealed-result = result-val sealed-value

stranded-result : Result stranded
stranded-result = result-ν sealed-result

stuckFun-value : Value stuckFun
stuckFun-value = stranded-result ↑[ zero ≔ zero ]
  adapter-region sealed-result

stuckFun-not-canonical : ¬ CanonicalFun stuckFun
stuckFun-not-canonical ()

stuck-not-result : ¬ Result stuck
stuck-not-result (result-val ())

stuck-not-blame : stuck ≢ blame
stuck-not-blame ()

stranded-no-step : ∀ {M′} → ¬ (crossedEnv ⊢ stranded —→ M′)
stranded-no-step = result-no-step stranded-result

stuckFun-no-step : ∀ {M′} → ¬ (baseEnv ⊢ stuckFun —→ M′)
stuckFun-no-step = value-no-step stuckFun-value

constant-no-step : ∀ {M′}
  → ¬ (baseEnv ⊢ $ (κℕ zero) —→ M′)
constant-no-step = value-no-step ($ (κℕ zero))

stuck-no-step : ∀ {M′} → ¬ (baseEnv ⊢ stuck —→ M′)
stuck-no-step (ξ-·₁ reduction) = stuckFun-no-step reduction
stuck-no-step (ξ-·₂ Vᵥ reduction) = constant-no-step reduction

stuck-no-progress : ¬ Progress baseEnv stuck
stuck-no-progress (step reduction) = stuck-no-step reduction
stuck-no-progress (done result) = stuck-not-result result

stranded-gap-witness :
  (baseEnv ∣ [] ⊢ stuck ⦂ ℕᵗ)
  × ¬ Progress baseEnv stuck
stranded-gap-witness = stuck-typed , stuck-no-progress
