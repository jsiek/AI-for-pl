module alt.probes.EagerSCWrapPreservationCounterexample where

-- File Charter:
--   * Checks whether U47b's eager SCWRAP contracta are typeable under the
--     current closed-crossing typing rules.
--   * The identity-function instances in both polarities are typed redexes,
--     while their specified contracta contain a bound variable beneath a
--     crossing and therefore cannot be typed.

open import Data.Fin using (zero)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
import Data.Vec.Base as Vec

open import Types
open import TermCtx
open import alt.Conversion
open import alt.ThetaTerms
open import alt.ThetaTyping
open import alt.ThetaReduction
open import alt.ThetaTermSubst using (rep?-here)

ℕᵗ : ∀ {Δ} → Ty Δ
ℕᵗ = ‵ `ℕ

ℕ⇒ℕ : ∀ {Δ} → Ty Δ
ℕ⇒ℕ = ℕᵗ ⇒ ℕᵗ

baseEnv : TyEnv 1 zero Vec.[]
baseEnv = ∅ ,:= ℕᵗ

no-live-anchor : ∀ {Θ} {α : TyVar Θ} → α ∉ᵛ Vec.[]
no-live-anchor ()

crossedEnv : TyEnv 1 1 (just zero Vec.∷ Vec.[])
crossedEnv = baseEnv ,begin[ zero ≔ zero ]⟨ no-live-anchor ⟩

revealRedex : Term 1 zero
revealRedex =
  (ƛ ℕᵗ ˙ ` zero) ↑[ zero ≔ zero ] (id↓ ↦↑ id↑)

revealContractum : Term 1 zero
revealContractum =
  ƛ ℕᵗ ˙
    (((` zero) [ (` zero) ↓[ zero ≔ zero ] id↓ ])
      ↑[ zero ≔ zero ] id↑)

revealRedex-typed : baseEnv ∣ [] ⊢ revealRedex ⦂ ℕ⇒ℕ
revealRedex-typed =
  ⊢reveal {fresh = no-live-anchor}
    (rep?-here {Ψ = baseEnv} {A = ℕᵗ})
    (⊢↑-⇒ (⊢id↓ (‵ `ℕ)) (⊢id↑ (‵ `ℕ)))
    (⊢ƛ (⊢` Z))

revealContractum-not-typed :
  ¬ (baseEnv ∣ [] ⊢ revealContractum ⦂ ℕ⇒ℕ)
revealContractum-not-typed
    (⊢ƛ (⊢reveal rep-eq c↑⊢
      (⊢conceal tyVar-eq ended-eq c↓⊢ (⊢` ()))))

revealBody-substitution-stops : ∀ (W : Term 1 zero)
  → ((((` zero) ↓[ zero ≔ zero ] id↓)
        ↑[ zero ≔ zero ] id↑) [ W ])
    ≡ ((` zero) ↓[ zero ≔ zero ] id↓) ↑[ zero ≔ zero ] id↑
revealBody-substitution-stops W = refl

concealRedex : Term 1 1
concealRedex =
  (ƛ ℕᵗ ˙ ` zero) ↓[ zero ≔ zero ] (id↑ ↦↓ id↓)

concealContractum : Term 1 1
concealContractum =
  ƛ ℕᵗ ˙
    (((` zero) [ (` zero) ↑[ zero ≔ zero ] id↑ ])
      ↓[ zero ≔ zero ] id↓)

concealRedex-typed : crossedEnv ∣ [] ⊢ concealRedex ⦂ ℕ⇒ℕ
concealRedex-typed =
  ⊢conceal refl refl
    (⊢↓-⇒ (⊢id↑ (‵ `ℕ)) (⊢id↓ (‵ `ℕ)))
    (⊢ƛ (⊢` Z))

concealContractum-not-typed :
  ¬ (crossedEnv ∣ [] ⊢ concealContractum ⦂ ℕ⇒ℕ)
concealContractum-not-typed
    (⊢ƛ (⊢conceal tyVar-eq ended-eq c↓⊢
      (⊢reveal rep-eq c↑⊢ (⊢` ()))))

concealBody-substitution-stops : ∀ (W : Term 1 1)
  → ((((` zero) ↑[ zero ≔ zero ] id↑)
        ↓[ zero ≔ zero ] id↓) [ W ])
    ≡ ((` zero) ↑[ zero ≔ zero ] id↑) ↓[ zero ≔ zero ] id↓
concealBody-substitution-stops W = refl
