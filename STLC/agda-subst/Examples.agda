module Examples where

-- File Charter:
--   * Closed STLC example terms with type-checking and evaluation tests.
--   * Uses `type-check-expect` for typing evidence and `eval` for outcomes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness; True)

open import STLC
open import Eval using (eval)
open import TypeCheckDec using (type-check-expect)

------------------------------------------------------------------------
-- Shared helpers
------------------------------------------------------------------------

expect-⊢ : (Γ : Ctx) → (M : Term) → (A : Ty)
  → True (type-check-expect Γ M A) → Γ ⊢ M ⦂ A
expect-⊢ Γ M A ok = toWitness {a? = type-check-expect Γ M A} ok

gas : ℕ
gas = 50

isNatValue : Term → Maybe ℕ
isNatValue `zero = just zeroℕ
isNatValue (`suc M) with isNatValue M
isNatValue (`suc M) | just n = just (sucℕ n)
isNatValue (`suc M) | nothing = nothing
isNatValue (` x) = nothing
isNatValue (ƛ A ⇒ N) = nothing
isNatValue (L · M) = nothing
isNatValue (case_[zero⇒_|suc⇒_] L M N) = nothing

evalNat : ∀ {M A} → (fuel : ℕ) → [] ⊢ M ⦂ A → Maybe ℕ
evalNat {M = M} fuel M⊢ with eval fuel M
... | just (N , trace) = isNatValue N
... | nothing = nothing

------------------------------------------------------------------------
-- Source-inspired reusable terms
------------------------------------------------------------------------

-- TAPL-style identity.
taplIdNat : Term
taplIdNat = ƛ nat ⇒ ` 0

taplIdNat-⊢ : [] ⊢ taplIdNat ⦂ (nat ⇒ nat)
taplIdNat-⊢ = expect-⊢ [] taplIdNat (nat ⇒ nat) tt

taplIdNatApp : Term
taplIdNatApp = taplIdNat · `zero

taplIdNatApp-⊢ : [] ⊢ taplIdNatApp ⦂ nat
taplIdNatApp-⊢ = expect-⊢ [] taplIdNatApp nat tt

taplIdNatApp-eval : evalNat gas taplIdNatApp-⊢ ≡ just zeroℕ
taplIdNatApp-eval = refl

-- TAPL-style constant function.
taplConstNat : Term
taplConstNat = ƛ nat ⇒ ƛ nat ⇒ ` 1

taplConstNat-⊢ : [] ⊢ taplConstNat ⦂ (nat ⇒ nat ⇒ nat)
taplConstNat-⊢ = expect-⊢ [] taplConstNat (nat ⇒ nat ⇒ nat) tt

taplConstNatApp : Term
taplConstNatApp = (taplConstNat · `zero) · (`suc `zero)

taplConstNatApp-⊢ : [] ⊢ taplConstNatApp ⦂ nat
taplConstNatApp-⊢ = expect-⊢ [] taplConstNatApp nat tt

taplConstNatApp-eval : evalNat gas taplConstNatApp-⊢ ≡ just zeroℕ
taplConstNatApp-eval = refl

-- TAPL-style successor function.
taplSuccNat : Term
taplSuccNat = ƛ nat ⇒ `suc ` 0

taplSuccNat-⊢ : [] ⊢ taplSuccNat ⦂ (nat ⇒ nat)
taplSuccNat-⊢ = expect-⊢ [] taplSuccNat (nat ⇒ nat) tt

taplSuccNatApp : Term
taplSuccNatApp = taplSuccNat · `zero

taplSuccNatApp-⊢ : [] ⊢ taplSuccNatApp ⦂ nat
taplSuccNatApp-⊢ = expect-⊢ [] taplSuccNatApp nat tt

taplSuccNatApp-eval : evalNat gas taplSuccNatApp-⊢ ≡ just (sucℕ zeroℕ)
taplSuccNatApp-eval = refl

-- PLFA-style case split that computes the identity on naturals.
plfaCaseNat : Term
plfaCaseNat = ƛ nat ⇒ (case_[zero⇒_|suc⇒_] (` 0) `zero (`suc (` 0)))

plfaCaseNat-⊢ : [] ⊢ plfaCaseNat ⦂ (nat ⇒ nat)
plfaCaseNat-⊢ = expect-⊢ [] plfaCaseNat (nat ⇒ nat) tt

plfaCaseNatApp : Term
plfaCaseNatApp = plfaCaseNat · (`suc `zero)

plfaCaseNatApp-⊢ : [] ⊢ plfaCaseNatApp ⦂ nat
plfaCaseNatApp-⊢ = expect-⊢ [] plfaCaseNatApp nat tt

plfaCaseNatApp-eval : evalNat gas plfaCaseNatApp-⊢ ≡ just (sucℕ zeroℕ)
plfaCaseNatApp-eval = refl

------------------------------------------------------------------------
-- Coverage index
------------------------------------------------------------------------

data Rule : Set where
  r-ξ-·₁ : Rule
  r-ξ-·₂ : Rule
  r-β-ƛ : Rule
  r-ξ-suc : Rule
  r-ξ-case : Rule
  r-β-zero : Rule
  r-β-suc : Rule

data ExampleId : Set where
  eid-xi-app1 : ExampleId
  eid-xi-app2 : ExampleId
  eid-beta-lam : ExampleId
  eid-xi-suc : ExampleId
  eid-xi-case : ExampleId
  eid-beta-zero : ExampleId
  eid-beta-suc : ExampleId

coverage : Rule -> ExampleId
coverage r-ξ-·₁ = eid-xi-app1
coverage r-ξ-·₂ = eid-xi-app2
coverage r-β-ƛ = eid-beta-lam
coverage r-ξ-suc = eid-xi-suc
coverage r-ξ-case = eid-xi-case
coverage r-β-zero = eid-beta-zero
coverage r-β-suc = eid-beta-suc

------------------------------------------------------------------------
-- Coverage examples
------------------------------------------------------------------------

-- `ξ-·₁`: the function position of an application reduces first.
ex-xi-app1 : Term
ex-xi-app1 = (case_[zero⇒_|suc⇒_] `zero taplIdNat taplIdNat) · `zero

ex-xi-app1-⊢ : [] ⊢ ex-xi-app1 ⦂ nat
ex-xi-app1-⊢ = expect-⊢ [] ex-xi-app1 nat tt

ex-xi-app1-eval : evalNat gas ex-xi-app1-⊢ ≡ just zeroℕ
ex-xi-app1-eval = refl

-- `ξ-·₂`: the argument position of an application reduces.
ex-xi-app2 : Term
ex-xi-app2 = taplIdNat · (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-app2-⊢ : [] ⊢ ex-xi-app2 ⦂ nat
ex-xi-app2-⊢ = expect-⊢ [] ex-xi-app2 nat tt

ex-xi-app2-eval : evalNat gas ex-xi-app2-⊢ ≡ just zeroℕ
ex-xi-app2-eval = refl

-- `β-ƛ`: ordinary lambda beta reduction.
ex-beta-lam : Term
ex-beta-lam = taplIdNatApp

ex-beta-lam-⊢ : [] ⊢ ex-beta-lam ⦂ nat
ex-beta-lam-⊢ = expect-⊢ [] ex-beta-lam nat tt

ex-beta-lam-eval : evalNat gas ex-beta-lam-⊢ ≡ just zeroℕ
ex-beta-lam-eval = refl

-- `ξ-suc`: reduce under `suc`.
ex-xi-suc : Term
ex-xi-suc = `suc (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-suc-⊢ : [] ⊢ ex-xi-suc ⦂ nat
ex-xi-suc-⊢ = expect-⊢ [] ex-xi-suc nat tt

ex-xi-suc-eval : evalNat gas ex-xi-suc-⊢ ≡ just (sucℕ zeroℕ)
ex-xi-suc-eval = refl

-- `ξ-case`: reduce the scrutinee of a case expression.
ex-xi-case : Term
ex-xi-case = case_[zero⇒_|suc⇒_] (taplIdNat · `zero) `zero (`suc `zero)

ex-xi-case-⊢ : [] ⊢ ex-xi-case ⦂ nat
ex-xi-case-⊢ = expect-⊢ [] ex-xi-case nat tt

ex-xi-case-eval : evalNat gas ex-xi-case-⊢ ≡ just zeroℕ
ex-xi-case-eval = refl

-- `β-zero`: case on zero.
ex-beta-zero : Term
ex-beta-zero = case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)

ex-beta-zero-⊢ : [] ⊢ ex-beta-zero ⦂ nat
ex-beta-zero-⊢ = expect-⊢ [] ex-beta-zero nat tt

ex-beta-zero-eval : evalNat gas ex-beta-zero-⊢ ≡ just zeroℕ
ex-beta-zero-eval = refl

-- `β-suc`: case on a successor value.
ex-beta-suc : Term
ex-beta-suc = case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc ` 0)

ex-beta-suc-⊢ : [] ⊢ ex-beta-suc ⦂ nat
ex-beta-suc-⊢ = expect-⊢ [] ex-beta-suc nat tt

ex-beta-suc-eval : evalNat gas ex-beta-suc-⊢ ≡ just (sucℕ zeroℕ)
ex-beta-suc-eval = refl

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- These examples are enough to exercise every STLC reduction rule
-- while also including TAPL-inspired and PLFA-inspired source shapes:
-- identity, constant, successor, and case-based identity.
