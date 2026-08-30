module alt.probes.U50SCWrapTyping where

-- File Charter:
--   * Checks the reveal-polarity U50 SCWRAP redex and contractum.
--   * The contractum's wrapper variable is born outside the reveal and
--     survives the matching conceal's positional context truncation.

open import Data.Fin using (zero)
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Vec.Base as Vec

open import Types
open import Consistency
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕᵗ

crossedEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossedEnv = baseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

outerCtx : TermCtx baseEnv
outerCtx = (ℕᵗ {Δ = zero} at currentScope baseEnv) ∷ []

outer-route :
  ScopeRoute baseEnv baseEnv empty
outer-route = currentScope baseEnv

outer-route-in-pocket :
  ScopeRoute baseEnv (crossedEnv ,end[ zero ]) empty
outer-route-in-pocket =
  scope-end
    (scope-begin outer-route (target-insert-empty zero))
    (target-delete-empty zero)

outerCtx-in-pocket : TermCtx (crossedEnv ,end[ zero ])
outerCtx-in-pocket = (ℕᵗ at outer-route-in-pocket) ∷ []

truncation-check :
  truncateForEnd (beginCtx outerCtx) zero ≡ outerCtx-in-pocket
truncation-check = refl

revealRedex : Term 1 zero
revealRedex =
  (ƛ ℕᵗ ˙ ` zero) ↑[ zero ≔ zero ] (id↓ ↦↑ id↑)

revealContractum : Term 1 zero
revealContractum =
  ƛ ℕᵗ ˙
    (((` zero) [ (` zero) ↓[ zero ≔ zero ] id↓ ])
      ↑[ zero ≔ zero ] id↑)

revealRedex-typed : baseEnv ∣ [] ⊢ revealRedex ⦂ ℕᵗ ⇒ ℕᵗ
revealRedex-typed =
  ⊢reveal {fresh = no-live-anchor}
    refl
    (⊢↑-⇒ (⊢id↓ (‵ `ℕ)) (⊢id↑ (‵ `ℕ)))
    (⊢ƛ (⊢` Z))

wrapper-typed : crossedEnv ∣ beginCtx outerCtx
  ⊢ (` zero) ↓[ zero ≔ zero ] id↓ ⦂ ℕᵗ
wrapper-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ))
    (⊢` Z)

revealContractum-typed :
  baseEnv ∣ [] ⊢ revealContractum ⦂ ℕᵗ ⇒ ℕᵗ
revealContractum-typed =
  ⊢ƛ
    (⊢reveal {fresh = no-live-anchor}
      refl
      (⊢id↑ (‵ `ℕ)) wrapper-typed)

revealRedex-step : baseEnv ⊢ revealRedex —→ revealContractum
revealRedex-step = SCWRAP refl

------------------------------------------------------------------------
-- A region-born binder is truncated above the wrapper pocket
------------------------------------------------------------------------

regionBinderCtx : TermCtx crossedEnv
regionBinderCtx =
  ((＇ (zero {n = 0})) at currentScope crossedEnv) ∷ beginCtx outerCtx

region-binder-truncates :
  truncateForEnd regionBinderCtx zero ≡ outerCtx-in-pocket
region-binder-truncates = refl

regionWrapper : Term 1 1
regionWrapper = (` zero) ↓[ zero ≔ zero ] id↓

regionWrapper-typed : crossedEnv ∣ regionBinderCtx
  ⊢ regionWrapper ⦂ ℕᵗ
regionWrapper-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ))
    (⊢` Z)

regionLambda-typed : crossedEnv ∣ beginCtx outerCtx
  ⊢ (ƛ (＇ zero) ˙ regionWrapper) ⦂ (＇ zero) ⇒ ℕᵗ
regionLambda-typed = ⊢ƛ regionWrapper-typed
