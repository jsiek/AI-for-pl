module ExamplesFresh where

-- File Charter:
--   * Closed example terms for extrinsic-inst PolyUpDown together with evaluation tests.
--   * Regression checks for representative casts, polymorphic instantiation, and
--   * blame behavior.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; z<s; s<s)
open import Data.Product using (_,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness; True)

open import Types
open import Store
open import UpDown
open import Terms
open import ReductionFresh
open import EvalPartialFresh
open import TypeCheckDec using (type-check-expect)

------------------------------------------------------------------------
-- Shared terms and helpers
------------------------------------------------------------------------

polyId : Term
polyId = Λ (ƛ (＇ 0) ⇒ ` 0)

idDyn : Term
idDyn = ƛ ★ ⇒ ` 0

nat : ℕ → Term
nat n = $ (κℕ n)

nat★ : ℕ → Term
nat★ n = nat n up tag (‵ `ℕ)

c : Term
c = nat 7

n42 : Term
n42 = nat 42

n69 : Term
n69 = nat 69

c★ : Term
c★ = nat★ 7

n42★ : Term
n42★ = nat★ 42

n69★ : Term
n69★ = nat★ 69

natId : Term
natId = ƛ (‵ `ℕ) ⇒ ` 0

idFun★ : Term
idFun★ = idDyn up tag (★ ⇒ ★)

polyApp : Term
polyApp =
  Λ
    (Λ
      (ƛ ((＇ 1) ⇒ (＇ 0)) ⇒
        ƛ (＇ 1) ⇒
          (` 1 · ` 0)))

polyK : Term
polyK = Λ (ƛ (＇ 0) ⇒ ƛ (＇ 0) ⇒ ` 1)

polyBetaId : Term
polyBetaId =
  Λ
    (ƛ (＇ 0) ⇒
      ((ƛ (＇ 0) ⇒ ` 0) · ` 0))

expect-⊢ :
  (M : Term) →
  (A : Ty) →
  True (type-check-expect 0 0 [] [] (λ ()) storeWf-∅ M A) →
  0 ∣ 0 ∣ [] ∣ [] ⊢ M ⦂ A
expect-⊢ M A ok =
  proj₁
    (toWitness {a? = type-check-expect 0 0 [] [] (λ ()) storeWf-∅ M A} ok)

gas : ℕ
gas = 250

isNatValue :
  Term →
  Maybe ℕ
isNatValue ($ (κℕ n)) = just n
isNatValue _ = nothing

isNatDynValue :
  Term →
  Maybe ℕ
isNatDynValue (V up d) = isNatDynValue V
isNatDynValue (V down d) = isNatDynValue V
isNatDynValue ($ (κℕ n)) = just n
isNatDynValue _ = nothing

isBlameValue :
  Term →
  Maybe Label
isBlameValue (blame ℓ) = just ℓ
isBlameValue _ = nothing

evalNat :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe ℕ
evalNat {Σ = Σ} {M = M} fuel M⊢ with eval? fuel Σ M
... | just (_ , (N , M↠N)) = isNatValue N
... | nothing = nothing

evalNatDyn :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe ℕ
evalNatDyn {Σ = Σ} {M = M} fuel M⊢ with eval? fuel Σ M
... | just (_ , (N , M↠N)) = isNatDynValue N
... | nothing = nothing

evalBlame :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe Label
evalBlame {Σ = Σ} {M = M} fuel M⊢ with eval? fuel Σ M
... | just (_ , (N , M↠N)) = isBlameValue N
... | nothing = nothing

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

example1-left : Term
example1-left = (idDyn · c★) down (untag (‵ `ℕ) 1)

example1-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example1-left ⦂ (‵ `ℕ)
example1-left-⊢ = expect-⊢ example1-left (‵ `ℕ) tt

example1-right : Term
example1-right = idDyn · c★

example1-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example1-right ⦂ ★
example1-right-⊢ = expect-⊢ example1-right ★ tt

example1-left-test : evalNat gas example1-left-⊢ ≡ just 7
example1-left-test = refl

example1-right-test : evalNatDyn gas example1-right-⊢ ≡ just 7
example1-right-test = refl

------------------------------------------------------------------------
-- Example 2
------------------------------------------------------------------------

example2-left : Term
example2-left = example1-left

example2-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example2-left ⦂ (‵ `ℕ)
example2-left-⊢ = expect-⊢ example2-left (‵ `ℕ) tt

example2-right : Term
example2-right = idDyn · c★

example2-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example2-right ⦂ ★
example2-right-⊢ = expect-⊢ example2-right ★ tt

example2-left-test : evalNat gas example2-left-⊢ ≡ just 7
example2-left-test = refl

example2-right-test : evalNatDyn gas example2-right-⊢ ≡ just 7
example2-right-test = refl

------------------------------------------------------------------------
-- Example 3
------------------------------------------------------------------------

example3-left : Term
example3-left = idDyn · c★

example3-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example3-left ⦂ ★
example3-left-⊢ = expect-⊢ example3-left ★ tt

example3-right : Term
example3-right = idDyn · c★

example3-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example3-right ⦂ ★
example3-right-⊢ = expect-⊢ example3-right ★ tt

example3-left-test : evalNatDyn gas example3-left-⊢ ≡ just 7
example3-left-test = refl

example3-right-test : evalNatDyn gas example3-right-⊢ ≡ just 7
example3-right-test = refl

------------------------------------------------------------------------
-- Example 4
------------------------------------------------------------------------

example4-left : Term
example4-left = example1-left

example4-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example4-left ⦂ (‵ `ℕ)
example4-left-⊢ = expect-⊢ example4-left (‵ `ℕ) tt

example4-right : Term
example4-right = example3-left

example4-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example4-right ⦂ ★
example4-right-⊢ = expect-⊢ example4-right ★ tt

example4-left-test : evalNat gas example4-left-⊢ ≡ just 7
example4-left-test = refl

example4-right-test : evalNatDyn gas example4-right-⊢ ≡ just 7
example4-right-test = refl

------------------------------------------------------------------------
-- Example 5 (cast up then down)
------------------------------------------------------------------------

example5-left : Term
example5-left = example1-left

example5-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example5-left ⦂ (‵ `ℕ)
example5-left-⊢ = expect-⊢ example5-left (‵ `ℕ) tt

example5-right : Term
example5-right =
  (example1-left up tag (‵ `ℕ)) down (untag (‵ `ℕ) 5)

example5-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example5-right ⦂ (‵ `ℕ)
example5-right-⊢ = expect-⊢ example5-right (‵ `ℕ) tt

example5-left-test : evalNat gas example5-left-⊢ ≡ just 7
example5-left-test = refl

example5-right-test : evalNat gas example5-right-⊢ ≡ just 7
example5-right-test = refl

------------------------------------------------------------------------
-- Example 6 (up, down, up)
------------------------------------------------------------------------

example6-left : Term
example6-left = example1-left

example6-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example6-left ⦂ (‵ `ℕ)
example6-left-⊢ = expect-⊢ example6-left (‵ `ℕ) tt

example6-right : Term
example6-right =
  (example1-right down (untag (‵ `ℕ) 6)) up tag (‵ `ℕ)

example6-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example6-right ⦂ ★
example6-right-⊢ = expect-⊢ example6-right ★ tt

example6-left-test : evalNat gas example6-left-⊢ ≡ just 7
example6-left-test = refl

example6-right-test : evalNatDyn gas example6-right-⊢ ≡ just 7
example6-right-test = refl

------------------------------------------------------------------------
-- Example 7 (up, down, up, down)
------------------------------------------------------------------------

example7-left : Term
example7-left = example1-left

example7-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example7-left ⦂ (‵ `ℕ)
example7-left-⊢ = expect-⊢ example7-left (‵ `ℕ) tt

example7-right : Term
example7-right =
  (example5-right up tag (‵ `ℕ)) down (untag (‵ `ℕ) 7)

example7-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example7-right ⦂ (‵ `ℕ)
example7-right-⊢ = expect-⊢ example7-right (‵ `ℕ) tt

example7-left-test : evalNat gas example7-left-⊢ ≡ just 7
example7-left-test = refl

example7-right-test : evalNat gas example7-right-⊢ ≡ just 7
example7-right-test = refl

------------------------------------------------------------------------
-- Example 8 (cast down on the right)
------------------------------------------------------------------------

example8-left : Term
example8-left = example1-left

example8-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example8-left ⦂ (‵ `ℕ)
example8-left-⊢ = expect-⊢ example8-left (‵ `ℕ) tt

example8-right : Term
example8-right = example1-left down id (‵ `ℕ)

example8-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example8-right ⦂ (‵ `ℕ)
example8-right-⊢ = expect-⊢ example8-right (‵ `ℕ) tt

example8-left-test : evalNat gas example8-left-⊢ ≡ just 7
example8-left-test = refl

example8-right-test : evalNat gas example8-right-⊢ ≡ just 7
example8-right-test = refl

------------------------------------------------------------------------
-- Example 9 (constant function)
------------------------------------------------------------------------

Kdyn : Term
Kdyn = ƛ ★ ⇒ ƛ ★ ⇒ ` 1

example9-left : Term
example9-left = ((Kdyn · n42★) · n69★) down (untag (‵ `ℕ) 9)

example9-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example9-left ⦂ (‵ `ℕ)
example9-left-⊢ = expect-⊢ example9-left (‵ `ℕ) tt

example9-right : Term
example9-right = (Kdyn · n42★) · n69★

example9-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example9-right ⦂ ★
example9-right-⊢ = expect-⊢ example9-right ★ tt

example9-left-test : evalNat gas example9-left-⊢ ≡ just 42
example9-left-test = refl

example9-right-test : evalNatDyn gas example9-right-⊢ ≡ just 42
example9-right-test = refl

------------------------------------------------------------------------
-- Example 10 (constant function, cast wrapper on right)
------------------------------------------------------------------------

example10-left : Term
example10-left = example9-left

example10-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example10-left ⦂ (‵ `ℕ)
example10-left-⊢ = expect-⊢ example10-left (‵ `ℕ) tt

example10-right : Term
example10-right = ((Kdyn up id (★ ⇒ ★ ⇒ ★)) · n42★) · n69★

example10-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example10-right ⦂ ★
example10-right-⊢ = expect-⊢ example10-right ★ tt

example10-left-test : evalNat gas example10-left-⊢ ≡ just 42
example10-left-test = refl

example10-right-test : evalNatDyn gas example10-right-⊢ ≡ just 42
example10-right-test = refl

------------------------------------------------------------------------
-- Example 12
------------------------------------------------------------------------

example12 : Term
example12 =
  ((c★ down (untag (‵ `ℕ) 12))
   up tag (‵ `ℕ))
  down (untag (‵ `ℕ) 12)

example12-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example12 ⦂ (‵ `ℕ)
example12-⊢ = expect-⊢ example12 (‵ `ℕ) tt

example12-test : evalNat gas example12-⊢ ≡ just 7
example12-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 2
------------------------------------------------------------------------

sec2-app-dyn : Term
sec2-app-dyn =
  (((polyApp ⦂∀ (`∀ (((＇ 1) ⇒ (＇ 0)) ⇒ ((＇ 1) ⇒ (＇ 0)))) [ ★ ])
     ⦂∀ ((★ ⇒ ＇ 0) ⇒ (★ ⇒ ＇ 0)) [ ★ ])
   · idDyn)
  · c★

sec2-app-dyn-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec2-app-dyn ⦂ ★
sec2-app-dyn-⊢ = expect-⊢ sec2-app-dyn ★ tt

sec2-app-base : Term
sec2-app-base =
  (((polyApp ⦂∀ (`∀ (((＇ 1) ⇒ (＇ 0)) ⇒ ((＇ 1) ⇒ (＇ 0)))) [ ‵ `ℕ ])
     ⦂∀ (((‵ `ℕ) ⇒ ＇ 0) ⇒ ((‵ `ℕ) ⇒ ＇ 0)) [ ‵ `ℕ ])
   · natId)
  · c

sec2-app-base-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec2-app-base ⦂ (‵ `ℕ)
sec2-app-base-⊢ = expect-⊢ sec2-app-base (‵ `ℕ) tt

sec2-app-dyn-test : evalNatDyn gas sec2-app-dyn-⊢ ≡ just 7
sec2-app-dyn-test = refl

sec2-app-base-test : evalNat gas sec2-app-base-⊢ ≡ just 7
sec2-app-base-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 5
------------------------------------------------------------------------

sec5-β : Term
sec5-β = (polyBetaId ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · c

sec5-β-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec5-β ⦂ (‵ `ℕ)
sec5-β-⊢ = expect-⊢ sec5-β (‵ `ℕ) tt

sec5-β-test : evalNat gas sec5-β-⊢ ≡ just 7
sec5-β-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 6
------------------------------------------------------------------------

sec6-K-dyn : Term
sec6-K-dyn =
  ((polyK ⦂∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0) [ ★ ]) · n42★) · n69★

sec6-K-dyn-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec6-K-dyn ⦂ ★
sec6-K-dyn-⊢ = expect-⊢ sec6-K-dyn ★ tt

sec6-K-base : Term
sec6-K-base =
  ((polyK ⦂∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · n42) · n69

sec6-K-base-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec6-K-base ⦂ (‵ `ℕ)
sec6-K-base-⊢ = expect-⊢ sec6-K-base (‵ `ℕ) tt

sec6-K-lax : Term
sec6-K-lax =
  (((polyK ⦂∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0) [ ★ ])
     down (tag (‵ `ℕ) ↦ ((id ★) ↦ untag (‵ `ℕ) 63)))
   · n42)
  · idFun★

sec6-K-lax-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec6-K-lax ⦂ (‵ `ℕ)
sec6-K-lax-⊢ = expect-⊢ sec6-K-lax (‵ `ℕ) tt

sec6-K-strict : Term
sec6-K-strict =
  (((polyK ⦂∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ])
     up ((id (‵ `ℕ)) ↦ (untag (‵ `ℕ) 64 ↦ (id (‵ `ℕ)))))
   · n42)
  · idFun★

sec6-K-strict-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec6-K-strict ⦂ (‵ `ℕ)
sec6-K-strict-⊢ = expect-⊢ sec6-K-strict (‵ `ℕ) tt

sec6-id-leak : Term
sec6-id-leak =
  ((idDyn down (ν (tag (｀ 0) ↦ id ★))) ⦂∀ (＇ 0 ⇒ ★) [ ‵ `ℕ ])
  · n42

sec6-id-leak-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec6-id-leak ⦂ ★
sec6-id-leak-⊢ = expect-⊢ sec6-id-leak ★ tt

sec6-K-dyn-test : evalNatDyn gas sec6-K-dyn-⊢ ≡ just 42
sec6-K-dyn-test = refl

sec6-K-base-test : evalNat gas sec6-K-base-⊢ ≡ just 42
sec6-K-base-test = refl

sec6-K-lax-test : evalNat gas sec6-K-lax-⊢ ≡ just 42
sec6-K-lax-test = refl

sec6-K-strict-test : evalBlame gas sec6-K-strict-⊢ ≡ just 64
sec6-K-strict-test = refl

-- Unlike the POPL'11 calculus, PolyUpDown currently allows this sealed
-- result to escape the surrounding `ν:=`, so evaluation reaches a
-- non-blame result.
sec6-id-leak-test : evalNatDyn gas sec6-id-leak-⊢ ≡ just 42
sec6-id-leak-test = refl


------------------------------------------------------------------------
-- Exploring invariants regarding seal names.
------------------------------------------------------------------------

seal-name-example : Term
seal-name-example =
  ((((Kdyn down (ν (ν (tag (｀ 1) ↦ (tag (｀ 0) ↦ untag (｀ 1) 700)))))
      ⦂∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ＇ 1)) [ ‵ `ℕ ])
     ⦂∀ ((‵ `ℕ) ⇒ ＇ 0 ⇒ (‵ `ℕ)) [ ‵ `ℕ ])
    · nat 42)
   · nat 0

seal-name-example-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ seal-name-example ⦂ (‵ `ℕ)
seal-name-example-⊢ = expect-⊢ seal-name-example (‵ `ℕ) tt

seal-name-example-test : evalNat gas seal-name-example-⊢ ≡ just 42
seal-name-example-test = refl

------------------------------------------------------------------------
-- Rule-coverage targets (one focused redex per currently-missing rule)
------------------------------------------------------------------------

target-β-up-∀ : Term
target-β-up-∀ =
  (nat 1 up (∀ᵖ (id (‵ `ℕ)))) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-tag-untag-bad : Term
target-tag-untag-bad =
  (nat 1 up tag (‵ `ℕ)) down (untag (‵ `𝔹) 501)

target-β-up-； : Term
target-β-up-； = nat 1 up (id (‵ `ℕ) ； id (‵ `ℕ))

target-β-down-； : Term
target-β-down-； = nat 1 down (id (‵ `ℕ) ； id (‵ `ℕ))

target-δ-⊕ : Term
target-δ-⊕ = nat 1 ⊕[ addℕ ] nat 2

target-blame-·₁ : Term
target-blame-·₁ = blame 502 · nat 0

target-blame-·₂ : Term
target-blame-·₂ = nat 0 · blame 503

target-blame-·α : Term
target-blame-·α = (blame 504) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-blame-down : Term
target-blame-down = (blame 505) down id ★

target-blame-⊕₁ : Term
target-blame-⊕₁ = blame 506 ⊕[ addℕ ] nat 0

target-blame-⊕₂ : Term
target-blame-⊕₂ = nat 0 ⊕[ addℕ ] blame 507

target-β-Λ : Term
target-β-Λ = (Λ (nat 0)) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-β-down-∀ : Term
target-β-down-∀ =
  (nat 0 down (∀ᵖ (id (‵ `ℕ)))) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-β-down-ν : Term
target-β-down-ν =
  (nat 0 down (ν (id (‵ `ℕ)))) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-β-up-ν : Term
target-β-up-ν = nat 0 up (ν (id ★))

target-ξ-·₂ : Term
target-ξ-·₂ = nat 0 · ((ƛ ★ ⇒ ` 0) · nat★ 1)

target-ξ-·α : Term
target-ξ-·α =
  ((ƛ ★ ⇒ ` 0) · nat★ 1) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

target-ξ-⊕₁ : Term
target-ξ-⊕₁ =
  ((ƛ ★ ⇒ ` 0) · nat★ 1) ⊕[ addℕ ] nat 0

target-ξ-⊕₂ : Term
target-ξ-⊕₂ =
  nat 0 ⊕[ addℕ ] ((ƛ ★ ⇒ ` 0) · nat★ 1)

------------------------------------------------------------------------
-- Three-seal allocation scenario:
--   1st allocation from β-up-ν
--   2nd allocation from β-down-ν
--   3rd allocation from β-up-ν
------------------------------------------------------------------------

three-seals-second-β-down-ν : Term
three-seals-second-β-down-ν =
  (((Λ (nat 0)) down (ν (id (`∀ ★))))
   up (ν (ν (id ★))))

at-least-three-allocs : List SealAllocTag → Bool
at-least-three-allocs (_ ∷ _ ∷ _ ∷ xs) = true
at-least-three-allocs _ = false

second-is-β-down-ν : List SealAllocTag → Bool
second-is-β-down-ν (_ ∷ alloc-β-down-ν ∷ xs) = true
second-is-β-down-ν _ = false

three-seals-alloc-trace : List SealAllocTag
three-seals-alloc-trace =
  alloc-trace-steps gas [] three-seals-second-β-down-ν

three-seals-has-at-least-three : Bool
three-seals-has-at-least-three = at-least-three-allocs three-seals-alloc-trace

three-seals-second-is-β-down-ν : Bool
three-seals-second-is-β-down-ν = second-is-β-down-ν three-seals-alloc-trace
