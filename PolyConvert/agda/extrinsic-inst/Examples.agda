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
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable.Core using (True; toWitness)

open import Types
open import Store
open import Imprecision
  using
    ( Imp
    ; _!
    ; _↦_
    ; id★
    ; idₓ_
    ; idι_
    ; ν_
    ; reflImp
    ; starImp
    ; ‵_!
    ; ‵∀_
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
ℕ⊑★ = (idι `ℕ) !

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

evalValue :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe ⊤
evalValue {Σ = Σ} {M = M} fuel M⊢ with eval? fuel Σ M
evalValue {Σ = Σ} {M = M} fuel M⊢ | nothing = nothing
evalValue {Σ = Σ} {M = M} fuel M⊢ | just (_ , (N , M↠N))
    with value? N
evalValue {Σ = Σ} {M = M} fuel M⊢ | just (_ , (N , M↠N))
    | just _ = just tt
evalValue {Σ = Σ} {M = M} fuel M⊢ | just (_ , (N , M↠N))
    | nothing = nothing

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
-- K through two incomparable lower-bound choices
------------------------------------------------------------------------

Kcoh-source-ty : Ty
Kcoh-source-ty = `∀ (＇ 0 ⇒ ★ ⇒ ＇ 0)

Kcoh-target-ty : Ty
Kcoh-target-ty = `∀ (★ ⇒ ＇ 0 ⇒ ★)

Kcoh-lower₁-ty : Ty
Kcoh-lower₁-ty = `∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ＇ 1))

Kcoh-lower₂-ty : Ty
Kcoh-lower₂-ty = `∀ (`∀ (＇ 0 ⇒ ＇ 1 ⇒ ＇ 0))

Kcoh-source : Term
Kcoh-source = Λ (ƛ (＇ 0) ⇒ ƛ ★ ⇒ ` 1)

Kcoh-source-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-source ⦂ Kcoh-source-ty
Kcoh-source-⊢ = expect-⊢ Kcoh-source Kcoh-source-ty tt

Kcoh-lower₁⊑source : Imp
Kcoh-lower₁⊑source =
  ‵∀ (ν ((idₓ 1) ↦ ((‵ 0 !) ↦ (idₓ 1))))

Kcoh-lower₁⊑target : Imp
Kcoh-lower₁⊑target =
  ν (‵∀ ((‵ 1 !) ↦ ((idₓ 0) ↦ (‵ 1 !))))

Kcoh-lower₂⊑source : Imp
Kcoh-lower₂⊑source =
  ν (‵∀ ((idₓ 0) ↦ ((‵ 1 !) ↦ (idₓ 0))))

Kcoh-lower₂⊑target : Imp
Kcoh-lower₂⊑target =
  ‵∀ (ν ((‵ 0 !) ↦ ((idₓ 1) ↦ (‵ 0 !))))

Kcoh-cast₁ : Term
Kcoh-cast₁ = (Kcoh-source ⇓ Kcoh-lower₁⊑source) ⇑ Kcoh-lower₁⊑target

Kcoh-cast₂ : Term
Kcoh-cast₂ = (Kcoh-source ⇓ Kcoh-lower₂⊑source) ⇑ Kcoh-lower₂⊑target

Kcoh-cast₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-cast₁ ⦂ Kcoh-target-ty
Kcoh-cast₁-⊢ = expect-⊢ Kcoh-cast₁ Kcoh-target-ty tt

Kcoh-cast₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-cast₂ ⦂ Kcoh-target-ty
Kcoh-cast₂-⊢ = expect-⊢ Kcoh-cast₂ Kcoh-target-ty tt

Kcoh-use₁ : Term
Kcoh-use₁ =
  ((Kcoh-cast₁ ⦂∀ (★ ⇒ ＇ 0 ⇒ ★) [ ‵ `ℕ ]) · n42★) · n69

Kcoh-use₂ : Term
Kcoh-use₂ =
  ((Kcoh-cast₂ ⦂∀ (★ ⇒ ＇ 0 ⇒ ★) [ ‵ `ℕ ]) · n42★) · n69

Kcoh-use₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-use₁ ⦂ ★
Kcoh-use₁-⊢ = expect-⊢ Kcoh-use₁ ★ tt

Kcoh-use₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-use₂ ⦂ ★
Kcoh-use₂-⊢ = expect-⊢ Kcoh-use₂ ★ tt

Kcoh-use₁-test : evalNatDyn gas Kcoh-use₁-⊢ ≡ just 42
Kcoh-use₁-test = refl

Kcoh-use₂-test : evalNatDyn gas Kcoh-use₂-⊢ ≡ just 42
Kcoh-use₂-test = refl

Kcoh-use★₁ : Term
Kcoh-use★₁ =
  ((Kcoh-cast₁ ⦂∀ (★ ⇒ ＇ 0 ⇒ ★) [ ★ ]) · n42★) · n69★

Kcoh-use★₂ : Term
Kcoh-use★₂ =
  ((Kcoh-cast₂ ⦂∀ (★ ⇒ ＇ 0 ⇒ ★) [ ★ ]) · n42★) · n69★

Kcoh-use★₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-use★₁ ⦂ ★
Kcoh-use★₁-⊢ = expect-⊢ Kcoh-use★₁ ★ tt

Kcoh-use★₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-use★₂ ⦂ ★
Kcoh-use★₂-⊢ = expect-⊢ Kcoh-use★₂ ★ tt

Kcoh-use★₁-test : evalNatDyn gas Kcoh-use★₁-⊢ ≡ just 42
Kcoh-use★₁-test = refl

Kcoh-use★₂-test : evalNatDyn gas Kcoh-use★₂-⊢ ≡ just 42
Kcoh-use★₂-test = refl

Kcoh-swap-source-ty : Ty
Kcoh-swap-source-ty = Kcoh-target-ty

Kcoh-swap-target-ty : Ty
Kcoh-swap-target-ty = Kcoh-source-ty

Kcoh-swap-source : Term
Kcoh-swap-source = Λ (ƛ ★ ⇒ ƛ (＇ 0) ⇒ ` 1)

Kcoh-swap-source-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-source ⦂ Kcoh-swap-source-ty
Kcoh-swap-source-⊢ = expect-⊢ Kcoh-swap-source Kcoh-swap-source-ty tt

Kcoh-swap-cast₁ : Term
Kcoh-swap-cast₁ =
  (Kcoh-swap-source ⇓ Kcoh-lower₁⊑target) ⇑ Kcoh-lower₁⊑source

Kcoh-swap-cast₂ : Term
Kcoh-swap-cast₂ =
  (Kcoh-swap-source ⇓ Kcoh-lower₂⊑target) ⇑ Kcoh-lower₂⊑source

Kcoh-swap-cast₁-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-cast₁ ⦂ Kcoh-swap-target-ty
Kcoh-swap-cast₁-⊢ =
  expect-⊢ Kcoh-swap-cast₁ Kcoh-swap-target-ty tt

Kcoh-swap-cast₂-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-cast₂ ⦂ Kcoh-swap-target-ty
Kcoh-swap-cast₂-⊢ =
  expect-⊢ Kcoh-swap-cast₂ Kcoh-swap-target-ty tt

Kcoh-swap-inst₁ : Term
Kcoh-swap-inst₁ =
  Kcoh-swap-cast₁ ⦂∀ (＇ 0 ⇒ ★ ⇒ ＇ 0) [ ‵ `ℕ ]

Kcoh-swap-inst₂ : Term
Kcoh-swap-inst₂ =
  Kcoh-swap-cast₂ ⦂∀ (＇ 0 ⇒ ★ ⇒ ＇ 0) [ ‵ `ℕ ]

Kcoh-swap-inst₁-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-inst₁ ⦂ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
Kcoh-swap-inst₁-⊢ =
  expect-⊢ Kcoh-swap-inst₁ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ) tt

Kcoh-swap-inst₂-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-inst₂ ⦂ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
Kcoh-swap-inst₂-⊢ =
  expect-⊢ Kcoh-swap-inst₂ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ) tt

Kcoh-swap-inst₁-value-test :
  evalValue gas Kcoh-swap-inst₁-⊢ ≡ just tt
Kcoh-swap-inst₁-value-test = refl

Kcoh-swap-inst₂-value-test :
  evalValue gas Kcoh-swap-inst₂-⊢ ≡ just tt
Kcoh-swap-inst₂-value-test = refl

Kcoh-swap-partial₁ : Term
Kcoh-swap-partial₁ = Kcoh-swap-inst₁ · n42

Kcoh-swap-partial₂ : Term
Kcoh-swap-partial₂ = Kcoh-swap-inst₂ · n42

Kcoh-swap-partial₁-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-partial₁ ⦂ (★ ⇒ ‵ `ℕ)
Kcoh-swap-partial₁-⊢ =
  expect-⊢ Kcoh-swap-partial₁ (★ ⇒ ‵ `ℕ) tt

Kcoh-swap-partial₂-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-partial₂ ⦂ (★ ⇒ ‵ `ℕ)
Kcoh-swap-partial₂-⊢ =
  expect-⊢ Kcoh-swap-partial₂ (★ ⇒ ‵ `ℕ) tt

Kcoh-swap-partial₁-value-test :
  evalValue gas Kcoh-swap-partial₁-⊢ ≡ just tt
Kcoh-swap-partial₁-value-test = refl

Kcoh-swap-partial₂-value-test :
  evalValue gas Kcoh-swap-partial₂-⊢ ≡ just tt
Kcoh-swap-partial₂-value-test = refl

Kcoh-swap-use₁ : Term
Kcoh-swap-use₁ =
  Kcoh-swap-partial₁ · n69★

Kcoh-swap-use₂ : Term
Kcoh-swap-use₂ =
  Kcoh-swap-partial₂ · n69★

Kcoh-swap-use₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-use₁ ⦂ (‵ `ℕ)
Kcoh-swap-use₁-⊢ = expect-⊢ Kcoh-swap-use₁ (‵ `ℕ) tt

Kcoh-swap-use₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-use₂ ⦂ (‵ `ℕ)
Kcoh-swap-use₂-⊢ = expect-⊢ Kcoh-swap-use₂ (‵ `ℕ) tt

Kcoh-swap-use₁-test : evalNat gas Kcoh-swap-use₁-⊢ ≡ just 42
Kcoh-swap-use₁-test = refl

Kcoh-swap-use₂-test : evalNat gas Kcoh-swap-use₂-⊢ ≡ just 42
Kcoh-swap-use₂-test = refl

Kcoh-swap-use★₁ : Term
Kcoh-swap-use★₁ =
  ((Kcoh-swap-cast₁ ⦂∀ (＇ 0 ⇒ ★ ⇒ ＇ 0) [ ★ ]) · n42★) · n69★

Kcoh-swap-use★₂ : Term
Kcoh-swap-use★₂ =
  ((Kcoh-swap-cast₂ ⦂∀ (＇ 0 ⇒ ★ ⇒ ＇ 0) [ ★ ]) · n42★) · n69★

Kcoh-swap-use★₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-use★₁ ⦂ ★
Kcoh-swap-use★₁-⊢ = expect-⊢ Kcoh-swap-use★₁ ★ tt

Kcoh-swap-use★₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-swap-use★₂ ⦂ ★
Kcoh-swap-use★₂-⊢ = expect-⊢ Kcoh-swap-use★₂ ★ tt

Kcoh-swap-use★₁-test : evalNatDyn gas Kcoh-swap-use★₁-⊢ ≡ just 42
Kcoh-swap-use★₁-test = refl

Kcoh-swap-use★₂-test : evalNatDyn gas Kcoh-swap-use★₂-⊢ ≡ just 42
Kcoh-swap-use★₂-test = refl

Kcoh-base-source-ty : Ty
Kcoh-base-source-ty = `∀ (★ ⇒ ＇ 0 ⇒ ‵ `ℕ)

Kcoh-base-target-ty : Ty
Kcoh-base-target-ty = `∀ (＇ 0 ⇒ ★ ⇒ ‵ `ℕ)

Kcoh-base-lower₁-ty : Ty
Kcoh-base-lower₁-ty = `∀ (`∀ (＇ 1 ⇒ ＇ 0 ⇒ ‵ `ℕ))

Kcoh-base-lower₂-ty : Ty
Kcoh-base-lower₂-ty = `∀ (`∀ (＇ 0 ⇒ ＇ 1 ⇒ ‵ `ℕ))

Kcoh-base-source : Term
Kcoh-base-source = Λ (ƛ ★ ⇒ ƛ (＇ 0) ⇒ n42)

Kcoh-base-source-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-base-source ⦂ Kcoh-base-source-ty
Kcoh-base-source-⊢ = expect-⊢ Kcoh-base-source Kcoh-base-source-ty tt

Kcoh-base-lower₁⊑source : Imp
Kcoh-base-lower₁⊑source =
  ν (‵∀ ((‵ 1 !) ↦ ((idₓ 0) ↦ (idι `ℕ))))

Kcoh-base-lower₁⊑target : Imp
Kcoh-base-lower₁⊑target =
  ‵∀ (ν ((idₓ 1) ↦ ((‵ 0 !) ↦ (idι `ℕ))))

Kcoh-base-lower₂⊑source : Imp
Kcoh-base-lower₂⊑source =
  ‵∀ (ν ((‵ 0 !) ↦ ((idₓ 1) ↦ (idι `ℕ))))

Kcoh-base-lower₂⊑target : Imp
Kcoh-base-lower₂⊑target =
  ν (‵∀ ((idₓ 0) ↦ ((‵ 1 !) ↦ (idι `ℕ))))

Kcoh-base-cast₁ : Term
Kcoh-base-cast₁ =
  (Kcoh-base-source ⇓ Kcoh-base-lower₁⊑source) ⇑
    Kcoh-base-lower₁⊑target

Kcoh-base-cast₂ : Term
Kcoh-base-cast₂ =
  (Kcoh-base-source ⇓ Kcoh-base-lower₂⊑source) ⇑
    Kcoh-base-lower₂⊑target

Kcoh-base-cast₁-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-base-cast₁ ⦂ Kcoh-base-target-ty
Kcoh-base-cast₁-⊢ = expect-⊢ Kcoh-base-cast₁ Kcoh-base-target-ty tt

Kcoh-base-cast₂-⊢ :
  0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-base-cast₂ ⦂ Kcoh-base-target-ty
Kcoh-base-cast₂-⊢ = expect-⊢ Kcoh-base-cast₂ Kcoh-base-target-ty tt

Kcoh-base-use₁ : Term
Kcoh-base-use₁ =
  ((Kcoh-base-cast₁ ⦂∀ (＇ 0 ⇒ ★ ⇒ ‵ `ℕ) [ ‵ `ℕ ]) · n69) · n42★

Kcoh-base-use₂ : Term
Kcoh-base-use₂ =
  ((Kcoh-base-cast₂ ⦂∀ (＇ 0 ⇒ ★ ⇒ ‵ `ℕ) [ ‵ `ℕ ]) · n69) · n42★

Kcoh-base-use₁-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-base-use₁ ⦂ (‵ `ℕ)
Kcoh-base-use₁-⊢ = expect-⊢ Kcoh-base-use₁ (‵ `ℕ) tt

Kcoh-base-use₂-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ Kcoh-base-use₂ ⦂ (‵ `ℕ)
Kcoh-base-use₂-⊢ = expect-⊢ Kcoh-base-use₂ (‵ `ℕ) tt

Kcoh-base-use₁-test : evalNat gas Kcoh-base-use₁-⊢ ≡ just 42
Kcoh-base-use₁-test = refl

Kcoh-base-use₂-test : evalNat gas Kcoh-base-use₂-⊢ ≡ just 42
Kcoh-base-use₂-test = refl

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
