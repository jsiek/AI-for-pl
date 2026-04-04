module Examples where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Sigma using (_,_)

open import STLC

infix 3 _∎
infixr 2 _—→⟨_⟩_

_∎ : (M : Term) -> M —↠ M
_∎ = ms-refl

_—→⟨_⟩_ : (L : Term) {M N : Term} ->
  L —→ M ->
  M —↠ N ->
  L —↠ N
L —→⟨ s ⟩ ms = ms-step L s ms

------------------------------------------------------------------------
-- Source-inspired reusable terms
------------------------------------------------------------------------

-- TAPL-style identity.
taplIdNat : Term
taplIdNat = ƛ nat ⇒ ` 0

taplIdNat-⊢ : ∀ {Γ : Context} -> HasType Γ taplIdNat (nat ⇒ nat)
taplIdNat-⊢ = tLam (tVar Z)

taplIdNatApp : Term
taplIdNatApp = taplIdNat · `zero

taplIdNatApp-⊢ : HasType [] taplIdNatApp nat
taplIdNatApp-⊢ = tApp taplIdNat-⊢ tZero

taplIdNatApp-↠ : taplIdNatApp —↠ `zero
taplIdNatApp-↠ = taplIdNatApp —→⟨ betaLam vZero ⟩ `zero ∎

-- TAPL-style constant function.
taplConstNat : Term
taplConstNat = ƛ nat ⇒ ƛ nat ⇒ ` 1

taplConstNat-⊢ : ∀ {Γ : Context} -> HasType Γ taplConstNat (nat ⇒ nat ⇒ nat)
taplConstNat-⊢ = tLam (tLam (tVar (S Z)))

taplConstNatApp : Term
taplConstNatApp = (taplConstNat · `zero) · (`suc `zero)

taplConstNatApp-⊢ : HasType [] taplConstNatApp nat
taplConstNatApp-⊢ =
  tApp
    (tApp taplConstNat-⊢ tZero)
    (tSuc tZero)

taplConstNatApp-↠ : taplConstNatApp —↠ `zero
taplConstNatApp-↠ =
  taplConstNatApp —→⟨ xiAppLeft (betaLam vZero) ⟩
  ((ƛ nat ⇒ `zero) · (`suc `zero)) —→⟨ betaLam (vSuc vZero) ⟩
  `zero ∎

-- TAPL-style successor function.
taplSuccNat : Term
taplSuccNat = ƛ nat ⇒ `suc ` 0

taplSuccNat-⊢ : ∀ {Γ : Context} -> HasType Γ taplSuccNat (nat ⇒ nat)
taplSuccNat-⊢ = tLam (tSuc (tVar Z))

taplSuccNatApp : Term
taplSuccNatApp = taplSuccNat · `zero

taplSuccNatApp-⊢ : HasType [] taplSuccNatApp nat
taplSuccNatApp-⊢ = tApp taplSuccNat-⊢ tZero

taplSuccNatApp-↠ : taplSuccNatApp —↠ (`suc `zero)
taplSuccNatApp-↠ = taplSuccNatApp —→⟨ betaLam vZero ⟩ (`suc `zero) ∎

-- PLFA-style case split that computes the identity on naturals.
plfaCaseNat : Term
plfaCaseNat = ƛ nat ⇒ (case_[zero⇒_|suc⇒_] (` 0) `zero (`suc (` 0)))

plfaCaseNat-⊢ : ∀ {Γ : Context} -> HasType Γ plfaCaseNat (nat ⇒ nat)
plfaCaseNat-⊢ = tLam (tCase (tVar Z) tZero (tSuc (tVar Z)))

plfaCaseNatApp : Term
plfaCaseNatApp = plfaCaseNat · (`suc `zero)

plfaCaseNatApp-⊢ : HasType [] plfaCaseNatApp nat
plfaCaseNatApp-⊢ = tApp plfaCaseNat-⊢ (tSuc tZero)

plfaCaseNatApp-↠ : plfaCaseNatApp —↠ (`suc `zero)
plfaCaseNatApp-↠ =
  plfaCaseNatApp —→⟨ betaLam (vSuc vZero) ⟩
  (case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc ` 0)) —→⟨ betaSuc vZero ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- Coverage index
------------------------------------------------------------------------

data Rule : Set where
  r-xiAppLeft : Rule
  r-xiAppRight : Rule
  r-betaLam : Rule
  r-xiSuc : Rule
  r-xiCase : Rule
  r-betaZero : Rule
  r-betaSuc : Rule

data ExampleId : Set where
  eid-xi-app1 : ExampleId
  eid-xi-app2 : ExampleId
  eid-beta-lam : ExampleId
  eid-xi-suc : ExampleId
  eid-xi-case : ExampleId
  eid-beta-zero : ExampleId
  eid-beta-suc : ExampleId

coverage : Rule -> ExampleId
coverage r-xiAppLeft = eid-xi-app1
coverage r-xiAppRight = eid-xi-app2
coverage r-betaLam = eid-beta-lam
coverage r-xiSuc = eid-xi-suc
coverage r-xiCase = eid-xi-case
coverage r-betaZero = eid-beta-zero
coverage r-betaSuc = eid-beta-suc

------------------------------------------------------------------------
-- Coverage examples
------------------------------------------------------------------------

-- `xiAppLeft`: the function position of an application reduces first.
ex-xi-app1 : Term
ex-xi-app1 = (case_[zero⇒_|suc⇒_] `zero taplIdNat taplIdNat) · `zero

ex-xi-app1-⊢ : HasType [] ex-xi-app1 nat
ex-xi-app1-⊢ =
  tApp
    (tCase tZero (taplIdNat-⊢ {Γ = []}) (taplIdNat-⊢ {Γ = nat ∷ []}))
    tZero

ex-xi-app1-↠ : ex-xi-app1 —↠ `zero
ex-xi-app1-↠ =
  ex-xi-app1 —→⟨ xiAppLeft betaZero ⟩
  (taplIdNat · `zero) —→⟨ betaLam vZero ⟩
  `zero ∎

-- `xiAppRight`: the argument position of an application reduces.
ex-xi-app2 : Term
ex-xi-app2 = taplIdNat · (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-app2-⊢ : HasType [] ex-xi-app2 nat
ex-xi-app2-⊢ = tApp taplIdNat-⊢ (tCase tZero tZero (tSuc tZero))

ex-xi-app2-↠ : ex-xi-app2 —↠ `zero
ex-xi-app2-↠ =
  ex-xi-app2 —→⟨ xiAppRight (vLam , betaZero) ⟩
  (taplIdNat · `zero) —→⟨ betaLam vZero ⟩
  `zero ∎

-- `betaLam`: ordinary lambda beta reduction.
ex-beta-lam : Term
ex-beta-lam = taplIdNatApp

ex-beta-lam-⊢ : HasType [] ex-beta-lam nat
ex-beta-lam-⊢ = taplIdNatApp-⊢

ex-beta-lam-↠ : ex-beta-lam —↠ `zero
ex-beta-lam-↠ = taplIdNatApp-↠

-- `xiSuc`: reduce under `suc`.
ex-xi-suc : Term
ex-xi-suc = `suc (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-suc-⊢ : HasType [] ex-xi-suc nat
ex-xi-suc-⊢ = tSuc (tCase tZero tZero (tSuc tZero))

ex-xi-suc-↠ : ex-xi-suc —↠ (`suc `zero)
ex-xi-suc-↠ =
  ex-xi-suc —→⟨ xiSuc betaZero ⟩
  (`suc `zero) ∎

-- `xiCase`: reduce the scrutinee of a case expression.
ex-xi-case : Term
ex-xi-case = case_[zero⇒_|suc⇒_] (taplIdNat · `zero) `zero (`suc `zero)

ex-xi-case-⊢ : HasType [] ex-xi-case nat
ex-xi-case-⊢ = tCase (tApp taplIdNat-⊢ tZero) tZero (tSuc tZero)

ex-xi-case-↠ : ex-xi-case —↠ `zero
ex-xi-case-↠ =
  ex-xi-case —→⟨ xiCase (betaLam vZero) ⟩
  (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)) —→⟨ betaZero ⟩
  `zero ∎

-- `betaZero`: case on zero.
ex-beta-zero : Term
ex-beta-zero = case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)

ex-beta-zero-⊢ : HasType [] ex-beta-zero nat
ex-beta-zero-⊢ = tCase tZero tZero (tSuc tZero)

ex-beta-zero-↠ : ex-beta-zero —↠ `zero
ex-beta-zero-↠ =
  ex-beta-zero —→⟨ betaZero ⟩
  `zero ∎

-- `betaSuc`: case on a successor value.
ex-beta-suc : Term
ex-beta-suc = case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc ` 0)

ex-beta-suc-⊢ : HasType [] ex-beta-suc nat
ex-beta-suc-⊢ = tCase (tSuc tZero) tZero (tSuc (tVar Z))

ex-beta-suc-↠ : ex-beta-suc —↠ (`suc `zero)
ex-beta-suc-↠ =
  ex-beta-suc —→⟨ betaSuc vZero ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- These examples are enough to exercise every STLC reduction rule
-- while also including TAPL-inspired and PLFA-inspired source shapes:
-- identity, constant, successor, and case-based identity.
