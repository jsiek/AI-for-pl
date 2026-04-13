module Examples where

open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Sigma using (_,_)

open import STLC

------------------------------------------------------------------------
-- Source-inspired reusable terms
------------------------------------------------------------------------

-- TAPL-style identity.
taplIdNat : Term
taplIdNat = ƛ nat ⇒ ` 0

taplIdNat-⊢ : ∀ {Γ : Ctx} -> Γ ⊢ taplIdNat ⦂ (nat ⇒ nat)
taplIdNat-⊢ = ⊢ƛ (⊢` Z)

taplIdNatApp : Term
taplIdNatApp = taplIdNat · `zero

taplIdNatApp-⊢ : [] ⊢ taplIdNatApp ⦂ nat
taplIdNatApp-⊢ = ⊢· taplIdNat-⊢ ⊢zero

taplIdNatApp-↠ : taplIdNatApp —↠ `zero
taplIdNatApp-↠ = taplIdNatApp —→⟨ β-ƛ `zero ⟩ `zero ∎

-- TAPL-style constant function.
taplConstNat : Term
taplConstNat = ƛ nat ⇒ ƛ nat ⇒ ` 1

taplConstNat-⊢ : ∀ {Γ : Ctx} -> Γ ⊢ taplConstNat ⦂ (nat ⇒ nat ⇒ nat)
taplConstNat-⊢ = ⊢ƛ (⊢ƛ (⊢` (S Z)))

taplConstNatApp : Term
taplConstNatApp = (taplConstNat · `zero) · (`suc `zero)

taplConstNatApp-⊢ : [] ⊢ taplConstNatApp ⦂ nat
taplConstNatApp-⊢ =
  ⊢·
    (⊢· taplConstNat-⊢ ⊢zero)
    (⊢suc ⊢zero)

taplConstNatApp-↠ : taplConstNatApp —↠ `zero
taplConstNatApp-↠ =
  taplConstNatApp —→⟨ ξ-·₁ (β-ƛ `zero) ⟩
  ((ƛ nat ⇒ `zero) · (`suc `zero)) —→⟨ β-ƛ (`suc `zero) ⟩
  `zero ∎

-- TAPL-style successor function.
taplSuccNat : Term
taplSuccNat = ƛ nat ⇒ `suc ` 0

taplSuccNat-⊢ : ∀ {Γ : Ctx} -> Γ ⊢ taplSuccNat ⦂ (nat ⇒ nat)
taplSuccNat-⊢ = ⊢ƛ (⊢suc (⊢` Z))

taplSuccNatApp : Term
taplSuccNatApp = taplSuccNat · `zero

taplSuccNatApp-⊢ : [] ⊢ taplSuccNatApp ⦂ nat
taplSuccNatApp-⊢ = ⊢· taplSuccNat-⊢ ⊢zero

taplSuccNatApp-↠ : taplSuccNatApp —↠ (`suc `zero)
taplSuccNatApp-↠ = taplSuccNatApp —→⟨ β-ƛ `zero ⟩ (`suc `zero) ∎

-- PLFA-style case split that computes the identity on naturals.
plfaCaseNat : Term
plfaCaseNat = ƛ nat ⇒ (case_[zero⇒_|suc⇒_] (` 0) `zero (`suc (` 0)))

plfaCaseNat-⊢ : ∀ {Γ : Ctx} -> Γ ⊢ plfaCaseNat ⦂ (nat ⇒ nat)
plfaCaseNat-⊢ = ⊢ƛ (⊢case (⊢` Z) ⊢zero (⊢suc (⊢` Z)))

plfaCaseNatApp : Term
plfaCaseNatApp = plfaCaseNat · (`suc `zero)

plfaCaseNatApp-⊢ : [] ⊢ plfaCaseNatApp ⦂ nat
plfaCaseNatApp-⊢ = ⊢· plfaCaseNat-⊢ (⊢suc ⊢zero)

plfaCaseNatApp-↠ : plfaCaseNatApp —↠ (`suc `zero)
plfaCaseNatApp-↠ =
  plfaCaseNatApp —→⟨ β-ƛ (`suc `zero) ⟩
  (case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc ` 0)) —→⟨ β-suc `zero ⟩
  (`suc `zero) ∎

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
ex-xi-app1-⊢ =
  ⊢·
    (⊢case ⊢zero (taplIdNat-⊢ {Γ = []}) (taplIdNat-⊢ {Γ = nat ∷ []}))
    ⊢zero

ex-xi-app1-↠ : ex-xi-app1 —↠ `zero
ex-xi-app1-↠ =
  ex-xi-app1 —→⟨ ξ-·₁ β-zero ⟩
  (taplIdNat · `zero) —→⟨ β-ƛ `zero ⟩
  `zero ∎

-- `ξ-·₂`: the argument position of an application reduces.
ex-xi-app2 : Term
ex-xi-app2 = taplIdNat · (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-app2-⊢ : [] ⊢ ex-xi-app2 ⦂ nat
ex-xi-app2-⊢ = ⊢· taplIdNat-⊢ (⊢case ⊢zero ⊢zero (⊢suc ⊢zero))

ex-xi-app2-↠ : ex-xi-app2 —↠ `zero
ex-xi-app2-↠ =
  ex-xi-app2 —→⟨ ξ-·₂ (ƛ _ ⇒ _ , β-zero) ⟩
  (taplIdNat · `zero) —→⟨ β-ƛ `zero ⟩
  `zero ∎

-- `β-ƛ`: ordinary lambda beta reduction.
ex-beta-lam : Term
ex-beta-lam = taplIdNatApp

ex-beta-lam-⊢ : [] ⊢ ex-beta-lam ⦂ nat
ex-beta-lam-⊢ = taplIdNatApp-⊢

ex-beta-lam-↠ : ex-beta-lam —↠ `zero
ex-beta-lam-↠ = taplIdNatApp-↠

-- `ξ-suc`: reduce under `suc`.
ex-xi-suc : Term
ex-xi-suc = `suc (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero))

ex-xi-suc-⊢ : [] ⊢ ex-xi-suc ⦂ nat
ex-xi-suc-⊢ = ⊢suc (⊢case ⊢zero ⊢zero (⊢suc ⊢zero))

ex-xi-suc-↠ : ex-xi-suc —↠ (`suc `zero)
ex-xi-suc-↠ =
  ex-xi-suc —→⟨ ξ-suc β-zero ⟩
  (`suc `zero) ∎

-- `ξ-case`: reduce the scrutinee of a case expression.
ex-xi-case : Term
ex-xi-case = case_[zero⇒_|suc⇒_] (taplIdNat · `zero) `zero (`suc `zero)

ex-xi-case-⊢ : [] ⊢ ex-xi-case ⦂ nat
ex-xi-case-⊢ = ⊢case (⊢· taplIdNat-⊢ ⊢zero) ⊢zero (⊢suc ⊢zero)

ex-xi-case-↠ : ex-xi-case —↠ `zero
ex-xi-case-↠ =
  ex-xi-case —→⟨ ξ-case (β-ƛ `zero) ⟩
  (case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)) —→⟨ β-zero ⟩
  `zero ∎

-- `β-zero`: case on zero.
ex-beta-zero : Term
ex-beta-zero = case_[zero⇒_|suc⇒_] `zero `zero (`suc `zero)

ex-beta-zero-⊢ : [] ⊢ ex-beta-zero ⦂ nat
ex-beta-zero-⊢ = ⊢case ⊢zero ⊢zero (⊢suc ⊢zero)

ex-beta-zero-↠ : ex-beta-zero —↠ `zero
ex-beta-zero-↠ =
  ex-beta-zero —→⟨ β-zero ⟩
  `zero ∎

-- `β-suc`: case on a successor value.
ex-beta-suc : Term
ex-beta-suc = case_[zero⇒_|suc⇒_] (`suc `zero) `zero (`suc ` 0)

ex-beta-suc-⊢ : [] ⊢ ex-beta-suc ⦂ nat
ex-beta-suc-⊢ = ⊢case (⊢suc ⊢zero) ⊢zero (⊢suc (⊢` Z))

ex-beta-suc-↠ : ex-beta-suc —↠ (`suc `zero)
ex-beta-suc-↠ =
  ex-beta-suc —→⟨ β-suc `zero ⟩
  (`suc `zero) ∎

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- These examples are enough to exercise every STLC reduction rule
-- while also including TAPL-inspired and PLFA-inspired source shapes:
-- identity, constant, successor, and case-based identity.
