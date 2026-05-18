module Examples where

-- File Charter:
--   * Closed example terms for extrinsic-inst PolyConvert.
--   * Ports representative examples from PolyUpDown's `ExamplesFresh` to the
--     current raw imprecision/conversion syntax.
--   * Provides typing derivations and executable evaluation checks for casts,
--     polymorphic instantiation, and store-threaded seal conversion.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (True; toWitness)

open import Types
open import Store
open import Imprecision
  using
    ( Imp
    ; A-⊑-★
    ; A⇒B-⊑-A′⇒B′
    ; ★-⊑-★
    ; ι-⊑-ι
    ; ∀A-⊑-B
    ; reflImp
    ; starImp
    )
open import Conversion
open import Primitives
open import Terms
open import Reduction
open import Eval
open import TypeCheckDec using (type-check-expect)

------------------------------------------------------------------------
-- Shared terms and helpers
------------------------------------------------------------------------

ℕ⊑★ : Imp
ℕ⊑★ = A-⊑-★ (ι-⊑-ι `ℕ)

polyId : Term
polyId = Λ (ƛ (＇ 0) ⇒ ` 0)

idDyn : Term
idDyn = ƛ ★ ⇒ ` 0

nat : ℕ → Term
nat n = $ (κℕ n)

nat★ : ℕ → Term
nat★ n = nat n ⇑ ℕ⊑★

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
idFun★ = idDyn ⇑ starImp (★ ⇒ ★)

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
  proj₁ (toWitness {a? = type-check-expect 0 0 [] [] (λ ()) storeWf-∅ M A} ok)

singletonℕStoreWf : StoreWf 0 1 ((zero , ‵ `ℕ) ∷ [])
singletonℕStoreWf = storeWf-ν-ext wfBase storeWf-∅

expect-⊢¹ :
  (M : Term) →
  (A : Ty) →
  True
    (type-check-expect
      0 1 ((zero , ‵ `ℕ) ∷ []) [] (λ ()) singletonℕStoreWf M A) →
  0 ∣ 1 ∣ ((zero , ‵ `ℕ) ∷ []) ∣ [] ⊢ M ⦂ A
expect-⊢¹ M A ok =
  proj₁
    (toWitness
      {a? =
        type-check-expect
          0 1 ((zero , ‵ `ℕ) ∷ []) [] (λ ()) singletonℕStoreWf M A}
      ok)

gas : ℕ
gas = 250

isNatValue : Term → Maybe ℕ
isNatValue ($ (κℕ n)) = just n
isNatValue _ = nothing

isNatDynValue : Term → Maybe ℕ
isNatDynValue (V ⇑ p) = isNatDynValue V
isNatDynValue (V ⇓ p) = isNatDynValue V
isNatDynValue (V ↑ c) = isNatDynValue V
isNatDynValue (V ↓ c) = isNatDynValue V
isNatDynValue ($ (κℕ n)) = just n
isNatDynValue _ = nothing

isBlameValue : Term → Maybe Label
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
-- Basic up/down examples
------------------------------------------------------------------------

example1-left : Term
example1-left = (idDyn · c★) ⇓ ℕ⊑★

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

example5-right : Term
example5-right = (example1-left ⇑ ℕ⊑★) ⇓ ℕ⊑★

example5-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example5-right ⦂ (‵ `ℕ)
example5-right-⊢ = expect-⊢ example5-right (‵ `ℕ) tt

example5-right-test : evalNat gas example5-right-⊢ ≡ just 7
example5-right-test = refl

example6-right : Term
example6-right = (example1-right ⇓ ℕ⊑★) ⇑ ℕ⊑★

example6-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example6-right ⦂ ★
example6-right-⊢ = expect-⊢ example6-right ★ tt

example6-right-test : evalNatDyn gas example6-right-⊢ ≡ just 7
example6-right-test = refl

example12 : Term
example12 = ((c★ ⇓ ℕ⊑★) ⇑ ℕ⊑★) ⇓ ℕ⊑★

example12-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example12 ⦂ (‵ `ℕ)
example12-⊢ = expect-⊢ example12 (‵ `ℕ) tt

example12-test : evalNat gas example12-⊢ ≡ just 7
example12-test = refl

------------------------------------------------------------------------
-- Constant function examples
------------------------------------------------------------------------

Kdyn : Term
Kdyn = ƛ ★ ⇒ ƛ ★ ⇒ ` 1

example9-left : Term
example9-left = ((Kdyn · n42★) · n69★) ⇓ ℕ⊑★

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

example10-right : Term
example10-right = ((Kdyn ⇑ reflImp (★ ⇒ ★ ⇒ ★)) · n42★) · n69★

example10-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example10-right ⦂ ★
example10-right-⊢ = expect-⊢ example10-right ★ tt

example10-right-test : evalNatDyn gas example10-right-⊢ ≡ just 42
example10-right-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11-style polymorphic examples
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

sec5-β : Term
sec5-β = (polyBetaId ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) · c

sec5-β-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ sec5-β ⦂ (‵ `ℕ)
sec5-β-⊢ = expect-⊢ sec5-β (‵ `ℕ) tt

sec5-β-test : evalNat gas sec5-β-⊢ ≡ just 7
sec5-β-test = refl

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

sec6-K-dyn-test : evalNatDyn gas sec6-K-dyn-⊢ ≡ just 42
sec6-K-dyn-test = refl

sec6-K-base-test : evalNat gas sec6-K-base-⊢ ≡ just 42
sec6-K-base-test = refl

------------------------------------------------------------------------
-- Store-threaded reveal/conceal conversion
------------------------------------------------------------------------

seal-roundtrip : Term
seal-roundtrip = ((polyId ⦂∀ (＇ 0 ⇒ ＇ 0) [ ‵ `ℕ ]) ↓ convert↓ (＇ 0 ⇒ ＇ 0) zero)
  ↑ convert↑ (＇ 0 ⇒ ＇ 0) zero

seal-roundtrip-⊢ :
  0 ∣ 1 ∣ ((zero , ‵ `ℕ) ∷ []) ∣ [] ⊢ seal-roundtrip ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
seal-roundtrip-⊢ =
  expect-⊢¹ seal-roundtrip (‵ `ℕ ⇒ ‵ `ℕ) tt

seal-roundtrip-app : Term
seal-roundtrip-app = seal-roundtrip · c

seal-roundtrip-app-⊢ :
  0 ∣ 1 ∣ ((zero , ‵ `ℕ) ∷ []) ∣ [] ⊢ seal-roundtrip-app ⦂ (‵ `ℕ)
seal-roundtrip-app-⊢ =
  ⊢· seal-roundtrip-⊢ (⊢$ (κℕ 7))

seal-roundtrip-app-test : evalNat gas seal-roundtrip-app-⊢ ≡ just 7
seal-roundtrip-app-test = refl
