module alt.probes.U50SCWrapTyping where

-- File Charter:
--   * Checks the reveal-polarity U50 SCWRAP redex and contractum.
--   * The contractum's wrapper variable is born outside the reveal and
--     survives the matching conceal's positional context truncation.

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
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

outerCtx : TermCtx
outerCtx = (ℕᵗ {Δ = zero} at currentScope baseEnv) ∷ []

outer-route :
  ScopeRoute (currentScope baseEnv) (scopeShape baseEnv) empty
outer-route = scope-here id↪-pointwise

outer-route-in-pocket :
  ScopeRoute (currentScope baseEnv)
    (scopeShape (crossedEnv ,end[ zero ])) empty
outer-route-in-pocket =
  scope-end
    (scope-begin outer-route target-insert-zero)
    target-delete-zero

truncation-check : truncateForEnd outerCtx crossedEnv zero ≡ outerCtx
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

wrapper-typed : crossedEnv ∣ outerCtx
  ⊢ (` zero) ↓[ zero ≔ zero ] id↓ ⦂ ℕᵗ
wrapper-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ))
    (⊢` (Z-at {ws = outer-route-in-pocket}))

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

regionBinderCtx : TermCtx
regionBinderCtx =
  ((＇ (zero {n = 0})) at currentScope crossedEnv) ∷ outerCtx

region-binder-truncates :
  truncateForEnd regionBinderCtx crossedEnv zero ≡ outerCtx
region-binder-truncates = refl

regionWrapper : Term 1 1
regionWrapper = (` zero) ↓[ zero ≔ zero ] id↓

regionWrapper-typed : crossedEnv ∣ regionBinderCtx
  ⊢ regionWrapper ⦂ ℕᵗ
regionWrapper-typed =
  ⊢conceal refl refl (⊢id↓ (‵ `ℕ))
    (⊢` (Z-at {ws = outer-route-in-pocket}))

regionLambda-typed : crossedEnv ∣ outerCtx
  ⊢ (ƛ (＇ zero) ˙ regionWrapper) ⦂ (＇ zero) ⇒ ℕᵗ
regionLambda-typed = ⊢ƛ regionWrapper-typed
