module Examples where

-- File Charter:
--   * Closed STLCMore example terms with type-checking and evaluation tests.
--   * Uses `type-check-expect` for typing evidence and `eval` for outcomes.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat
  renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable.Core using (toWitness; True)

open import STLCMore
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
isNatValue (M as A) = nothing
isNatValue (let' M `in N) = nothing
isNatValue (case_[zero⇒_|suc⇒_] L M N) = nothing
isNatValue `unit = nothing
isNatValue (pair M , N) = nothing
isNatValue (fst M) = nothing
isNatValue (snd M) = nothing
isNatValue (inl M `to A) = nothing
isNatValue (inr M `to A) = nothing
isNatValue (case⊎_[inl⇒_|inr⇒_] L M N) = nothing

evalNat : ∀ {M A} → (fuel : ℕ) → [] ⊢ M ⦂ A → Maybe ℕ
evalNat {M = M} fuel M⊢ with eval fuel M
... | just (N , trace) = isNatValue N
... | nothing = nothing

isUnitValue : Term → Maybe ⊤
isUnitValue `unit = just tt
isUnitValue `zero = nothing
isUnitValue (`suc M) = nothing
isUnitValue (` x) = nothing
isUnitValue (ƛ A ⇒ N) = nothing
isUnitValue (L · M) = nothing
isUnitValue (M as A) = nothing
isUnitValue (let' M `in N) = nothing
isUnitValue (case_[zero⇒_|suc⇒_] L M N) = nothing
isUnitValue (pair M , N) = nothing
isUnitValue (fst M) = nothing
isUnitValue (snd M) = nothing
isUnitValue (inl M `to A) = nothing
isUnitValue (inr M `to A) = nothing
isUnitValue (case⊎_[inl⇒_|inr⇒_] L M N) = nothing

evalUnit : ∀ {M A} → (fuel : ℕ) → [] ⊢ M ⦂ A → Maybe ⊤
evalUnit {M = M} fuel M⊢ with eval fuel M
... | just (N , trace) = isUnitValue N
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

-- TAPL-style Unit literal.
taplUnit : Term
taplUnit = `unit

taplUnit-⊢ : [] ⊢ taplUnit ⦂ unit
taplUnit-⊢ = expect-⊢ [] taplUnit unit tt

taplUnit-eval : evalUnit gas taplUnit-⊢ ≡ just tt
taplUnit-eval = refl

-- TAPL Chapter 11 derived sequencing form.
taplSeqNat : Term
taplSeqNat = `unit ； `suc `zero

taplSeqNat-⊢ : [] ⊢ taplSeqNat ⦂ nat
taplSeqNat-⊢ = expect-⊢ [] taplSeqNat nat tt

taplSeqNat-eval : evalNat gas taplSeqNat-⊢ ≡ just (sucℕ zeroℕ)
taplSeqNat-eval = refl

taplAscribeNat : Term
taplAscribeNat = (`suc `zero) as nat

taplAscribeNat-⊢ : [] ⊢ taplAscribeNat ⦂ nat
taplAscribeNat-⊢ = expect-⊢ [] taplAscribeNat nat tt

taplAscribeNat-eval : evalNat gas taplAscribeNat-⊢ ≡ just (sucℕ zeroℕ)
taplAscribeNat-eval = refl

taplLetNat : Term
taplLetNat = let' (`suc `zero) `in (`suc (` 0))

taplLetNat-⊢ : [] ⊢ taplLetNat ⦂ nat
taplLetNat-⊢ = expect-⊢ [] taplLetNat nat tt

taplLetNat-eval : evalNat gas taplLetNat-⊢ ≡ just (sucℕ (sucℕ zeroℕ))
taplLetNat-eval = refl

-- TAPL Chapter 11 pair projection examples.
taplPairFirstNat : Term
taplPairFirstNat = fst (pair (`suc `zero) , `unit)

taplPairFirstNat-⊢ : [] ⊢ taplPairFirstNat ⦂ nat
taplPairFirstNat-⊢ = expect-⊢ [] taplPairFirstNat nat tt

taplPairFirstNat-eval :
  evalNat gas taplPairFirstNat-⊢ ≡ just (sucℕ zeroℕ)
taplPairFirstNat-eval = refl

taplPairSecondUnit : Term
taplPairSecondUnit = snd (pair (`suc `zero) , `unit)

taplPairSecondUnit-⊢ : [] ⊢ taplPairSecondUnit ⦂ unit
taplPairSecondUnit-⊢ = expect-⊢ [] taplPairSecondUnit unit tt

taplPairSecondUnit-eval : evalUnit gas taplPairSecondUnit-⊢ ≡ just tt
taplPairSecondUnit-eval = refl

-- TAPL Chapter 11 sum case examples.
taplSumLeftNat : Term
taplSumLeftNat =
  case⊎_[inl⇒_|inr⇒_] (inl (`suc `zero) `to (nat `+ unit)) (` 0) `zero

taplSumLeftNat-⊢ : [] ⊢ taplSumLeftNat ⦂ nat
taplSumLeftNat-⊢ = expect-⊢ [] taplSumLeftNat nat tt

taplSumLeftNat-eval : evalNat gas taplSumLeftNat-⊢ ≡ just (sucℕ zeroℕ)
taplSumLeftNat-eval = refl

taplSumRightNat : Term
taplSumRightNat =
  case⊎_[inl⇒_|inr⇒_] (inr `unit `to (nat `+ unit)) (` 0) `zero

taplSumRightNat-⊢ : [] ⊢ taplSumRightNat ⦂ nat
taplSumRightNat-⊢ = expect-⊢ [] taplSumRightNat nat tt

taplSumRightNat-eval : evalNat gas taplSumRightNat-⊢ ≡ just zeroℕ
taplSumRightNat-eval = refl

------------------------------------------------------------------------
-- Coverage index
------------------------------------------------------------------------

data Rule : Set where
  r-ξ-·₁ : Rule
  r-ξ-·₂ : Rule
  r-β-ƛ : Rule
  r-ξ-as : Rule
  r-β-as : Rule
  r-ξ-let : Rule
  r-β-let : Rule
  r-ξ-suc : Rule
  r-ξ-case : Rule
  r-β-zero : Rule
  r-β-suc : Rule
  r-ξ-pair₁ : Rule
  r-ξ-pair₂ : Rule
  r-ξ-fst : Rule
  r-β-fst : Rule
  r-ξ-snd : Rule
  r-β-snd : Rule
  r-ξ-inl : Rule
  r-ξ-inr : Rule
  r-ξ-case⊎ : Rule
  r-β-inl : Rule
  r-β-inr : Rule

data ExampleId : Set where
  eid-xi-app1 : ExampleId
  eid-xi-app2 : ExampleId
  eid-beta-lam : ExampleId
  eid-xi-as : ExampleId
  eid-beta-as : ExampleId
  eid-xi-let : ExampleId
  eid-beta-let : ExampleId
  eid-xi-suc : ExampleId
  eid-xi-case : ExampleId
  eid-beta-zero : ExampleId
  eid-beta-suc : ExampleId
  eid-xi-pair1 : ExampleId
  eid-xi-pair2 : ExampleId
  eid-xi-fst : ExampleId
  eid-beta-fst : ExampleId
  eid-xi-snd : ExampleId
  eid-beta-snd : ExampleId
  eid-xi-inl : ExampleId
  eid-xi-inr : ExampleId
  eid-xi-case-sum : ExampleId
  eid-beta-inl : ExampleId
  eid-beta-inr : ExampleId

coverage : Rule -> ExampleId
coverage r-ξ-·₁ = eid-xi-app1
coverage r-ξ-·₂ = eid-xi-app2
coverage r-β-ƛ = eid-beta-lam
coverage r-ξ-as = eid-xi-as
coverage r-β-as = eid-beta-as
coverage r-ξ-let = eid-xi-let
coverage r-β-let = eid-beta-let
coverage r-ξ-suc = eid-xi-suc
coverage r-ξ-case = eid-xi-case
coverage r-β-zero = eid-beta-zero
coverage r-β-suc = eid-beta-suc
coverage r-ξ-pair₁ = eid-xi-pair1
coverage r-ξ-pair₂ = eid-xi-pair2
coverage r-ξ-fst = eid-xi-fst
coverage r-β-fst = eid-beta-fst
coverage r-ξ-snd = eid-xi-snd
coverage r-β-snd = eid-beta-snd
coverage r-ξ-inl = eid-xi-inl
coverage r-ξ-inr = eid-xi-inr
coverage r-ξ-case⊎ = eid-xi-case-sum
coverage r-β-inl = eid-beta-inl
coverage r-β-inr = eid-beta-inr

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

-- `ξ-as`: reduce the ascribed term before dropping the ascription.
ex-xi-as : Term
ex-xi-as = (taplIdNat · `zero) as nat

ex-xi-as-⊢ : [] ⊢ ex-xi-as ⦂ nat
ex-xi-as-⊢ = expect-⊢ [] ex-xi-as nat tt

ex-xi-as-eval : evalNat gas ex-xi-as-⊢ ≡ just zeroℕ
ex-xi-as-eval = refl

-- `β-as`: ascription of a value erases at runtime.
ex-beta-as : Term
ex-beta-as = taplAscribeNat

ex-beta-as-⊢ : [] ⊢ ex-beta-as ⦂ nat
ex-beta-as-⊢ = expect-⊢ [] ex-beta-as nat tt

ex-beta-as-eval : evalNat gas ex-beta-as-⊢ ≡ just (sucℕ zeroℕ)
ex-beta-as-eval = refl

-- `ξ-let`: reduce the bound term before substitution.
ex-xi-let : Term
ex-xi-let = let' (taplIdNat · `zero) `in (`suc (` 0))

ex-xi-let-⊢ : [] ⊢ ex-xi-let ⦂ nat
ex-xi-let-⊢ = expect-⊢ [] ex-xi-let nat tt

ex-xi-let-eval : evalNat gas ex-xi-let-⊢ ≡ just (sucℕ zeroℕ)
ex-xi-let-eval = refl

-- `β-let`: substitute a value into the let body.
ex-beta-let : Term
ex-beta-let = taplLetNat

ex-beta-let-⊢ : [] ⊢ ex-beta-let ⦂ nat
ex-beta-let-⊢ = expect-⊢ [] ex-beta-let nat tt

ex-beta-let-eval :
  evalNat gas ex-beta-let-⊢ ≡ just (sucℕ (sucℕ zeroℕ))
ex-beta-let-eval = refl

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

-- `ξ-pair₁`: reduce the first component of a pair.
ex-xi-pair1 : Term
ex-xi-pair1 = fst (pair (taplIdNat · `zero) , `unit)

ex-xi-pair1-⊢ : [] ⊢ ex-xi-pair1 ⦂ nat
ex-xi-pair1-⊢ = expect-⊢ [] ex-xi-pair1 nat tt

ex-xi-pair1-eval : evalNat gas ex-xi-pair1-⊢ ≡ just zeroℕ
ex-xi-pair1-eval = refl

-- `ξ-pair₂`: after the first component is a value, reduce the second.
ex-xi-pair2 : Term
ex-xi-pair2 = snd (pair `zero , (taplIdNat · (`suc `zero)))

ex-xi-pair2-⊢ : [] ⊢ ex-xi-pair2 ⦂ nat
ex-xi-pair2-⊢ = expect-⊢ [] ex-xi-pair2 nat tt

ex-xi-pair2-eval : evalNat gas ex-xi-pair2-⊢ ≡ just (sucℕ zeroℕ)
ex-xi-pair2-eval = refl

-- `ξ-fst`: reduce the pair-producing term before projecting.
ex-xi-fst : Term
ex-xi-fst =
  fst (case_[zero⇒_|suc⇒_] `zero (pair `zero , `unit) (pair ` 0 , `unit))

ex-xi-fst-⊢ : [] ⊢ ex-xi-fst ⦂ nat
ex-xi-fst-⊢ = expect-⊢ [] ex-xi-fst nat tt

ex-xi-fst-eval : evalNat gas ex-xi-fst-⊢ ≡ just zeroℕ
ex-xi-fst-eval = refl

-- `β-fst`: project the first component from a pair value.
ex-beta-fst : Term
ex-beta-fst = taplPairFirstNat

ex-beta-fst-⊢ : [] ⊢ ex-beta-fst ⦂ nat
ex-beta-fst-⊢ = expect-⊢ [] ex-beta-fst nat tt

ex-beta-fst-eval : evalNat gas ex-beta-fst-⊢ ≡ just (sucℕ zeroℕ)
ex-beta-fst-eval = refl

-- `ξ-snd`: reduce the pair-producing term before projecting.
ex-xi-snd : Term
ex-xi-snd =
  snd (case_[zero⇒_|suc⇒_] `zero (pair `zero , `unit) (pair ` 0 , `unit))

ex-xi-snd-⊢ : [] ⊢ ex-xi-snd ⦂ unit
ex-xi-snd-⊢ = expect-⊢ [] ex-xi-snd unit tt

ex-xi-snd-eval : evalUnit gas ex-xi-snd-⊢ ≡ just tt
ex-xi-snd-eval = refl

-- `β-snd`: project the second component from a pair value.
ex-beta-snd : Term
ex-beta-snd = taplPairSecondUnit

ex-beta-snd-⊢ : [] ⊢ ex-beta-snd ⦂ unit
ex-beta-snd-⊢ = expect-⊢ [] ex-beta-snd unit tt

ex-beta-snd-eval : evalUnit gas ex-beta-snd-⊢ ≡ just tt
ex-beta-snd-eval = refl

-- `ξ-inl`: reduce inside a left injection.
ex-xi-inl : Term
ex-xi-inl =
  case⊎_[inl⇒_|inr⇒_]
    (inl (taplIdNat · `zero) `to (nat `+ unit))
    (`suc (` 0))
    `zero

ex-xi-inl-⊢ : [] ⊢ ex-xi-inl ⦂ nat
ex-xi-inl-⊢ = expect-⊢ [] ex-xi-inl nat tt

ex-xi-inl-eval : evalNat gas ex-xi-inl-⊢ ≡ just (sucℕ zeroℕ)
ex-xi-inl-eval = refl

-- `ξ-inr`: reduce inside a right injection.
ex-xi-inr : Term
ex-xi-inr =
  case⊎_[inl⇒_|inr⇒_]
    (inr (`unit ； `unit) `to (nat `+ unit))
    (` 0)
    `zero

ex-xi-inr-⊢ : [] ⊢ ex-xi-inr ⦂ nat
ex-xi-inr-⊢ = expect-⊢ [] ex-xi-inr nat tt

ex-xi-inr-eval : evalNat gas ex-xi-inr-⊢ ≡ just zeroℕ
ex-xi-inr-eval = refl

-- `ξ-case⊎`: reduce the scrutinee before sum elimination.
ex-xi-case-sum : Term
ex-xi-case-sum =
  case⊎_[inl⇒_|inr⇒_]
    (case⊎_[inl⇒_|inr⇒_]
      (inl `zero `to (nat `+ unit))
      (inl (`suc (` 0)) `to (nat `+ unit))
      (inr (` 0) `to (nat `+ unit)))
    (` 0)
    `zero

ex-xi-case-sum-⊢ : [] ⊢ ex-xi-case-sum ⦂ nat
ex-xi-case-sum-⊢ = expect-⊢ [] ex-xi-case-sum nat tt

ex-xi-case-sum-eval :
  evalNat gas ex-xi-case-sum-⊢ ≡ just (sucℕ zeroℕ)
ex-xi-case-sum-eval = refl

-- `β-inl`: choose the left branch and substitute the left payload.
ex-beta-inl : Term
ex-beta-inl = taplSumLeftNat

ex-beta-inl-⊢ : [] ⊢ ex-beta-inl ⦂ nat
ex-beta-inl-⊢ = expect-⊢ [] ex-beta-inl nat tt

ex-beta-inl-eval : evalNat gas ex-beta-inl-⊢ ≡ just (sucℕ zeroℕ)
ex-beta-inl-eval = refl

-- `β-inr`: choose the right branch and substitute the right payload.
ex-beta-inr : Term
ex-beta-inr = taplSumRightNat

ex-beta-inr-⊢ : [] ⊢ ex-beta-inr ⦂ nat
ex-beta-inr-⊢ = expect-⊢ [] ex-beta-inr nat tt

ex-beta-inr-eval : evalNat gas ex-beta-inr-⊢ ≡ just zeroℕ
ex-beta-inr-eval = refl

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- These examples are enough to exercise every STLCMore reduction rule
-- while also including TAPL-inspired and PLFA-inspired source shapes:
-- identity, constant, successor, ascription, let, pair projection, sum
-- injection/elimination, and case-based identity.
