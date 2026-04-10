module Examples where

-- File Charter:
--   * Closed example terms for extrinsic PolyUpDown together with evaluation tests.
--   * Regression checks for representative casts, polymorphic instantiation, and
--   * blame behavior.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; z<s; s<s)
open import Data.Product using (_,_; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (tt)

open import Types
open import Store
open import UpDown
open import Terms
open import Reduction
open import Eval

------------------------------------------------------------------------
-- Shared terms and helpers
------------------------------------------------------------------------

term-of :
  ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Term
term-of {M = M} M⊢ = M

polyId : Term
polyId = Λ (ƛ (＇ zero) ⇒ ` zero)

polyId-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ polyId ⦂ (`∀ (＇ zero ⇒ ＇ zero))
polyId-⊢ = ⊢Λ (⊢ƛ (wfVar z<s) (⊢` Z))

idDyn : Term
idDyn = ƛ ★ ⇒ ` zero

idDyn-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ idDyn ⦂ (★ ⇒ ★)
idDyn-⊢ = ⊢ƛ wf★ (⊢` Z)

nat : ℕ → Term
nat n = $ (κℕ n)

nat-⊢ : ∀ {Ψ}{Σ : Store} (n : ℕ) → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ nat n ⦂ (‵ `ℕ)
nat-⊢ n = ⊢$ (κℕ n)

nat★ : ℕ → Term
nat★ n = nat n up tag (‵ `ℕ)

nat★-⊢ : ∀ {Ψ}{Σ : Store} (n : ℕ) → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ nat★ n ⦂ ★
nat★-⊢ n = ⊢up (nat-⊢ n) (wt-tag (‵ `ℕ) tt)

c : Term
c = nat 7

c-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ c ⦂ (‵ `ℕ)
c-⊢ = nat-⊢ 7

n42 : Term
n42 = nat 42

n42-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ n42 ⦂ (‵ `ℕ)
n42-⊢ = nat-⊢ 42

n69 : Term
n69 = nat 69

n69-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ n69 ⦂ (‵ `ℕ)
n69-⊢ = nat-⊢ 69

c★ : Term
c★ = nat★ 7

c★-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ c★ ⦂ ★
c★-⊢ = nat★-⊢ 7

n42★ : Term
n42★ = nat★ 42

n42★-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ n42★ ⦂ ★
n42★-⊢ = nat★-⊢ 42

n69★ : Term
n69★ = nat★ 69

n69★-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ n69★ ⦂ ★
n69★-⊢ = nat★-⊢ 69

natId : Term
natId = ƛ (‵ `ℕ) ⇒ ` zero

natId-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ natId ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
natId-⊢ = ⊢ƛ wfBase (⊢` Z)

idFun★ : Term
idFun★ = idDyn up tag (★ ⇒ ★)

idFun★-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ idFun★ ⦂ ★
idFun★-⊢ = ⊢up idDyn-⊢ (wt-tag ★⇒★ tt)

polyApp : Term
polyApp =
  Λ
    (Λ
      (ƛ ((＇ (suc zero)) ⇒ (＇ zero)) ⇒
        ƛ (＇ (suc zero)) ⇒
          (` (suc zero) · ` zero)))

polyApp-⊢ :
  ∀ {Ψ}{Σ : Store} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢
    polyApp
    ⦂ (`∀ (`∀ (((＇ (suc zero)) ⇒ (＇ zero)) ⇒ ((＇ (suc zero)) ⇒ (＇ zero)))))
polyApp-⊢ =
  ⊢Λ
    (⊢Λ
      (⊢ƛ
        (wf⇒ (wfVar (s<s z<s)) (wfVar z<s))
        (⊢ƛ
          (wfVar (s<s z<s))
          (⊢· (⊢` (S Z)) (⊢` Z)))))

polyK : Term
polyK = Λ (ƛ (＇ zero) ⇒ ƛ (＇ zero) ⇒ ` (suc zero))

polyK-⊢ :
  ∀ {Ψ}{Σ : Store} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ polyK ⦂ (`∀ (＇ zero ⇒ ＇ zero ⇒ ＇ zero))
polyK-⊢ =
  ⊢Λ
    (⊢ƛ
      (wfVar z<s)
      (⊢ƛ (wfVar z<s) (⊢` (S Z))))

polyBetaId : Term
polyBetaId =
  Λ
    (ƛ (＇ zero) ⇒
      ((ƛ (＇ zero) ⇒ ` zero) · ` zero))

polyBetaId-⊢ :
  ∀ {Ψ}{Σ : Store} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ polyBetaId ⦂ (`∀ (＇ zero ⇒ ＇ zero))
polyBetaId-⊢ =
  ⊢Λ
    (⊢ƛ
      (wfVar z<s)
      (⊢·
        (⊢ƛ (wfVar z<s) (⊢` Z))
        (⊢` Z)))

kDyn-to-nat★nat :
  ∀ {Ψ}{Σ : Store} →
  (ℓ : Label) →
  Σ ∣ every Ψ ∣ every Ψ ⊢
    (tag (‵ `ℕ) ↦ (id ↦ untag (‵ `ℕ) ℓ))
    ⦂ (★ ⇒ ★ ⇒ ★) ⊒ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
kDyn-to-nat★nat ℓ =
  wt-↦ {p = tag (‵ `ℕ)} {q = id ↦ untag (‵ `ℕ) ℓ}
    (wt-tag (‵ `ℕ) tt)
    (wt-↦ {p = id} {q = untag (‵ `ℕ) ℓ}
      wt-id
      (wt-untag (‵ `ℕ) tt ℓ))

kNat-to-nat★nat :
  ∀ {Ψ}{Σ : Store} →
  (ℓ : Label) →
  Σ ∣ every Ψ ∣ every Ψ ⊢
    (id ↦ (untag (‵ `ℕ) ℓ ↦ id))
    ⦂ (‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ) ⊑ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
kNat-to-nat★nat ℓ =
  wt-↦ {p = id} {q = untag (‵ `ℕ) ℓ ↦ id}
    wt-id
    (wt-↦ {p = untag (‵ `ℕ) ℓ} {q = id}
      (wt-untag (‵ `ℕ) tt ℓ)
      wt-id)

idDyn-to-∀X-X⇒★ :
  ∀ {Ψ}{Σ : Store} →
  Σ ∣ every Ψ ∣ every Ψ ⊢ _ ⦂ (★ ⇒ ★) ⊒ (`∀ (＇ zero ⇒ ★))
idDyn-to-∀X-X⇒★ =
  wt-ν
    (wt-↦ {p = tag (｀ zero)} {q = id}
      (wt-tag (｀ zero) here)
      wt-id)

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
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe ℕ
evalNat {Ψ} {Σ} {M} {A} uΣ fuel M⊢ with eval uΣ fuel M⊢
... | r = isNatValue (proj₁ (proj₂ (proj₂ r)))

evalNatDyn :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe ℕ
evalNatDyn {Ψ} {Σ} {M} {A} uΣ fuel M⊢ with eval uΣ fuel M⊢
... | r = isNatDynValue (proj₁ (proj₂ (proj₂ r)))

evalBlame :
  ∀ {Ψ}{Σ : Store}{M : Term}{A : Ty} →
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M⊢ : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ M ⦂ A) →
  Maybe Label
evalBlame {Ψ} {Σ} {M} {A} uΣ fuel M⊢ with eval uΣ fuel M⊢
... | r = isBlameValue (proj₁ (proj₂ (proj₂ r)))

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

example1-left : Term
example1-left = (idDyn · c★) down (untag (‵ `ℕ) 1)

example1-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example1-left ⦂ (‵ `ℕ)
example1-left-⊢ =
  ⊢down
    (⊢· idDyn-⊢ c★-⊢)
    (wt-untag (‵ `ℕ) tt 1)

example1-right : Term
example1-right = idDyn · c★

example1-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example1-right ⦂ ★
example1-right-⊢ = ⊢· idDyn-⊢ c★-⊢

example1-left-test : evalNat uniq[] gas example1-left-⊢ ≡ just 7
example1-left-test = refl

example1-right-test : evalNatDyn uniq[] gas example1-right-⊢ ≡ just 7
example1-right-test = refl

------------------------------------------------------------------------
-- Example 2
------------------------------------------------------------------------

example2-left : Term
example2-left = example1-left

example2-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example2-left ⦂ (‵ `ℕ)
example2-left-⊢ = example1-left-⊢

example2-right : Term
example2-right = idDyn · c★

example2-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example2-right ⦂ ★
example2-right-⊢ = ⊢· idDyn-⊢ c★-⊢

example2-left-test : evalNat uniq[] gas example2-left-⊢ ≡ just 7
example2-left-test = refl

example2-right-test : evalNatDyn uniq[] gas example2-right-⊢ ≡ just 7
example2-right-test = refl

------------------------------------------------------------------------
-- Example 3
------------------------------------------------------------------------

example3-left : Term
example3-left = idDyn · c★

example3-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example3-left ⦂ ★
example3-left-⊢ = ⊢· idDyn-⊢ c★-⊢

example3-right : Term
example3-right = idDyn · c★

example3-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example3-right ⦂ ★
example3-right-⊢ = ⊢· idDyn-⊢ c★-⊢

example3-left-test : evalNatDyn uniq[] gas example3-left-⊢ ≡ just 7
example3-left-test = refl

example3-right-test : evalNatDyn uniq[] gas example3-right-⊢ ≡ just 7
example3-right-test = refl

------------------------------------------------------------------------
-- Example 4
------------------------------------------------------------------------

example4-left : Term
example4-left = example1-left

example4-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example4-left ⦂ (‵ `ℕ)
example4-left-⊢ = example1-left-⊢

example4-right : Term
example4-right = example3-left

example4-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example4-right ⦂ ★
example4-right-⊢ = example3-left-⊢

example4-left-test : evalNat uniq[] gas example4-left-⊢ ≡ just 7
example4-left-test = refl

example4-right-test : evalNatDyn uniq[] gas example4-right-⊢ ≡ just 7
example4-right-test = refl

------------------------------------------------------------------------
-- Example 5 (cast up then down)
------------------------------------------------------------------------

example5-left : Term
example5-left = example1-left

example5-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example5-left ⦂ (‵ `ℕ)
example5-left-⊢ = example1-left-⊢

example5-right : Term
example5-right =
  (example1-left up tag (‵ `ℕ)) down (untag (‵ `ℕ) 5)

example5-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example5-right ⦂ (‵ `ℕ)
example5-right-⊢ =
  ⊢down
    (⊢up example1-left-⊢ (wt-tag (‵ `ℕ) tt))
    (wt-untag (‵ `ℕ) tt 5)

example5-left-test : evalNat uniq[] gas example5-left-⊢ ≡ just 7
example5-left-test = refl

example5-right-test : evalNat uniq[] gas example5-right-⊢ ≡ just 7
example5-right-test = refl

------------------------------------------------------------------------
-- Example 6 (up, down, up)
------------------------------------------------------------------------

example6-left : Term
example6-left = example1-left

example6-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example6-left ⦂ (‵ `ℕ)
example6-left-⊢ = example1-left-⊢

example6-right : Term
example6-right =
  (example1-right down (untag (‵ `ℕ) 6)) up tag (‵ `ℕ)

example6-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example6-right ⦂ ★
example6-right-⊢ =
  ⊢up
    (⊢down example1-right-⊢ (wt-untag (‵ `ℕ) tt 6))
    (wt-tag (‵ `ℕ) tt)

example6-left-test : evalNat uniq[] gas example6-left-⊢ ≡ just 7
example6-left-test = refl

example6-right-test : evalNatDyn uniq[] gas example6-right-⊢ ≡ just 7
example6-right-test = refl

------------------------------------------------------------------------
-- Example 7 (up, down, up, down)
------------------------------------------------------------------------

example7-left : Term
example7-left = example1-left

example7-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example7-left ⦂ (‵ `ℕ)
example7-left-⊢ = example1-left-⊢

example7-right : Term
example7-right =
  (example5-right up tag (‵ `ℕ)) down (untag (‵ `ℕ) 7)

example7-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example7-right ⦂ (‵ `ℕ)
example7-right-⊢ =
  ⊢down
    (⊢up example5-right-⊢ (wt-tag (‵ `ℕ) tt))
    (wt-untag (‵ `ℕ) tt 7)

example7-left-test : evalNat uniq[] gas example7-left-⊢ ≡ just 7
example7-left-test = refl

example7-right-test : evalNat uniq[] gas example7-right-⊢ ≡ just 7
example7-right-test = refl

------------------------------------------------------------------------
-- Example 8 (cast down on the right)
------------------------------------------------------------------------

example8-left : Term
example8-left = example1-left

example8-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example8-left ⦂ (‵ `ℕ)
example8-left-⊢ = example1-left-⊢

example8-right : Term
example8-right = example1-left down id

example8-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example8-right ⦂ (‵ `ℕ)
example8-right-⊢ = ⊢down example1-left-⊢ wt-id

example8-left-test : evalNat uniq[] gas example8-left-⊢ ≡ just 7
example8-left-test = refl

example8-right-test : evalNat uniq[] gas example8-right-⊢ ≡ just 7
example8-right-test = refl

------------------------------------------------------------------------
-- Example 9 (constant function)
------------------------------------------------------------------------

Kdyn : Term
Kdyn = ƛ ★ ⇒ ƛ ★ ⇒ ` (suc zero)

Kdyn-⊢ : ∀ {Ψ}{Σ : Store} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ Kdyn ⦂ (★ ⇒ ★ ⇒ ★)
Kdyn-⊢ = ⊢ƛ wf★ (⊢ƛ wf★ (⊢` (S Z)))

example9-left : Term
example9-left = ((Kdyn · n42★) · n69★) down (untag (‵ `ℕ) 9)

example9-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example9-left ⦂ (‵ `ℕ)
example9-left-⊢ =
  ⊢down
    (⊢· (⊢· Kdyn-⊢ n42★-⊢) n69★-⊢)
    (wt-untag (‵ `ℕ) tt 9)

example9-right : Term
example9-right = (Kdyn · n42★) · n69★

example9-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example9-right ⦂ ★
example9-right-⊢ = ⊢· (⊢· Kdyn-⊢ n42★-⊢) n69★-⊢

example9-left-test : evalNat uniq[] gas example9-left-⊢ ≡ just 42
example9-left-test = refl

example9-right-test : evalNatDyn uniq[] gas example9-right-⊢ ≡ just 42
example9-right-test = refl

------------------------------------------------------------------------
-- Example 10 (constant function, cast wrapper on right)
------------------------------------------------------------------------

example10-left : Term
example10-left = example9-left

example10-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example10-left ⦂ (‵ `ℕ)
example10-left-⊢ = example9-left-⊢

example10-right : Term
example10-right = ((Kdyn up id) · n42★) · n69★

example10-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example10-right ⦂ ★
example10-right-⊢ = ⊢· (⊢· (⊢up Kdyn-⊢ wt-id) n42★-⊢) n69★-⊢

example10-left-test : evalNat uniq[] gas example10-left-⊢ ≡ just 42
example10-left-test = refl

example10-right-test : evalNatDyn uniq[] gas example10-right-⊢ ≡ just 42
example10-right-test = refl

------------------------------------------------------------------------
-- Example 11 (nested ν)
------------------------------------------------------------------------

example11-left : Term
example11-left =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙ c)

example11-left-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example11-left ⦂ (‵ `ℕ)
example11-left-⊢ = ⊢ν wfBase (⊢ν wfBase c-⊢)

example11-right : Term
example11-right = (ƛ ★ ⇒ ((ƛ ★ ⇒ ` zero) · ` zero)) · c★

example11-right-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example11-right ⦂ ★
example11-right-⊢ =
  ⊢·
    (⊢ƛ
      wf★
      (⊢·
        (⊢ƛ wf★ (⊢` Z))
        (⊢` Z)))
    c★-⊢

example11-left-test : evalNat uniq[] gas example11-left-⊢ ≡ just 7
example11-left-test = refl

example11-right-test : evalNatDyn uniq[] gas example11-right-⊢ ≡ just 7
example11-right-test = refl

------------------------------------------------------------------------
-- Example 12
------------------------------------------------------------------------

example12 : Term
example12 =
  ((c★ down (untag (‵ `ℕ) 12))
   up tag (‵ `ℕ))
  down (untag (‵ `ℕ) 12)

example12-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example12 ⦂ (‵ `ℕ)
example12-⊢ =
  ⊢down
    (⊢up
      (⊢down c★-⊢ (wt-untag (‵ `ℕ) tt 12))
      (wt-tag (‵ `ℕ) tt))
    (wt-untag (‵ `ℕ) tt 12)

example12-test : evalNat uniq[] gas example12-⊢ ≡ just 7
example12-test = refl

------------------------------------------------------------------------
-- Example 13 (same tag succeeds, mixed tag blames)
------------------------------------------------------------------------

example13-good : Term
example13-good =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙
      (((c★ down (untag (‵ `ℕ) 13))
        up tag (‵ `ℕ))
       down (untag (‵ `ℕ) 13)))

example13-good-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example13-good ⦂ (‵ `ℕ)
example13-good-⊢ =
  ⊢ν
    wfBase
    (⊢ν
      wfBase
      (⊢down
        (⊢up
          (⊢down c★-⊢ (wt-untag (‵ `ℕ) tt 13))
          (wt-tag (‵ `ℕ) tt))
        (wt-untag (‵ `ℕ) tt 13)))

example13-mixed : Term
example13-mixed =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙
      (c★ down (untag (‵ `𝔹) 13)))

example13-mixed-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ example13-mixed ⦂ (‵ `𝔹)
example13-mixed-⊢ =
  ⊢ν
    wfBase
    (⊢ν
      wfBase
      (⊢down c★-⊢ (wt-untag (‵ `𝔹) tt 13)))

example13-good-test : evalNat uniq[] gas example13-good-⊢ ≡ just 7
example13-good-test = refl

example13-mixed-test : evalBlame uniq[] gas example13-mixed-⊢ ≡ just 13
example13-mixed-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 2
------------------------------------------------------------------------

sec2-app-dyn-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ ★
sec2-app-dyn-⊢ = ⊢· (⊢· (inst-wt _ ★ _ (inst-wt _ ★ _ polyApp-⊢ wf★) wf★) idDyn-⊢) c★-⊢

sec2-app-dyn : Term
sec2-app-dyn = term-of sec2-app-dyn-⊢

sec2-app-base-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ (‵ `ℕ)
sec2-app-base-⊢ =
  ⊢·
    (⊢·
      (inst-wt _ (‵ `ℕ) _ (inst-wt _ (‵ `ℕ) _ polyApp-⊢ wfBase) wfBase)
      natId-⊢)
    c-⊢

sec2-app-base : Term
sec2-app-base = term-of sec2-app-base-⊢

sec2-app-dyn-test : evalNatDyn uniq[] gas sec2-app-dyn-⊢ ≡ just 7
sec2-app-dyn-test = refl

sec2-app-base-test : evalNat uniq[] gas sec2-app-base-⊢ ≡ just 7
sec2-app-base-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 5
------------------------------------------------------------------------

sec5-β-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ (‵ `ℕ)
sec5-β-⊢ = ⊢· (inst-wt polyBetaId (‵ `ℕ) (＇ zero ⇒ ＇ zero) polyBetaId-⊢ wfBase) c-⊢

sec5-β : Term
sec5-β = term-of sec5-β-⊢

sec5-β-test : evalNat uniq[] gas sec5-β-⊢ ≡ just 7
sec5-β-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 6
------------------------------------------------------------------------

sec6-K-dyn-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ ★
sec6-K-dyn-⊢ = ⊢· (⊢· (inst-wt polyK ★ (＇ zero ⇒ ＇ zero ⇒ ＇ zero) polyK-⊢ wf★) n42★-⊢) n69★-⊢

sec6-K-dyn : Term
sec6-K-dyn = term-of sec6-K-dyn-⊢

sec6-K-base-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ (‵ `ℕ)
sec6-K-base-⊢ = ⊢· (⊢· (inst-wt polyK (‵ `ℕ) (＇ zero ⇒ ＇ zero ⇒ ＇ zero) polyK-⊢ wfBase) n42-⊢) n69-⊢

sec6-K-base : Term
sec6-K-base = term-of sec6-K-base-⊢

sec6-K-lax-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ (‵ `ℕ)
sec6-K-lax-⊢ =
  ⊢·
    (⊢·
      (⊢down
        (inst-wt polyK ★ (＇ zero ⇒ ＇ zero ⇒ ＇ zero) polyK-⊢ wf★)
        (kDyn-to-nat★nat 63))
      n42-⊢)
    idFun★-⊢

sec6-K-lax : Term
sec6-K-lax = term-of sec6-K-lax-⊢

sec6-K-strict-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ (‵ `ℕ)
sec6-K-strict-⊢ =
  ⊢·
    (⊢·
      (⊢up
        (inst-wt polyK (‵ `ℕ) (＇ zero ⇒ ＇ zero ⇒ ＇ zero) polyK-⊢ wfBase)
        (kNat-to-nat★nat 64))
      n42-⊢)
    idFun★-⊢

sec6-K-strict : Term
sec6-K-strict = term-of sec6-K-strict-⊢

sec6-id-leak-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ _ ⦂ ★
sec6-id-leak-⊢ =
  ⊢·
    (inst-wt _ (‵ `ℕ) _ (⊢down idDyn-⊢ idDyn-to-∀X-X⇒★) wfBase)
    n42-⊢

sec6-id-leak : Term
sec6-id-leak = term-of sec6-id-leak-⊢

sec6-K-dyn-test : evalNatDyn uniq[] gas sec6-K-dyn-⊢ ≡ just 42
sec6-K-dyn-test = refl

sec6-K-base-test : evalNat uniq[] gas sec6-K-base-⊢ ≡ just 42
sec6-K-base-test = refl

sec6-K-lax-test : evalNat uniq[] gas sec6-K-lax-⊢ ≡ just 42
sec6-K-lax-test = refl

sec6-K-strict-test : evalBlame uniq[] gas sec6-K-strict-⊢ ≡ just 64
sec6-K-strict-test = refl

-- Unlike the POPL'11 calculus, PolyUpDown currently allows this sealed
-- result to escape the surrounding `ν:=`, so evaluation reaches a
-- non-blame result.
sec6-id-leak-test : evalNatDyn uniq[] gas sec6-id-leak-⊢ ≡ just 42
sec6-id-leak-test = refl


------------------------------------------------------------------------
-- Exploring invariants regarding seal names.
------------------------------------------------------------------------

kDyn-to-∀X-∀Y-X⇒Y⇒X :
  ∀ {Ψ}{Σ : Store} →
  Σ ∣ every Ψ ∣ every Ψ
  ⊢ (ν (ν (tag (｀ (suc zero)) ↦ (tag (｀ zero) ↦ untag (｀ (suc zero)) 700))))
  ⦂ (★ ⇒ ★ ⇒ ★) ⊒ (`∀ (`∀ (＇ (suc zero) ⇒ ＇ zero ⇒ ＇ (suc zero))))
kDyn-to-∀X-∀Y-X⇒Y⇒X =
  wt-ν
    (wt-ν
      (wt-↦
        (wt-tag (｀ (suc zero)) (there here))
        (wt-↦
          (wt-tag (｀ zero) here)
          (wt-untag (｀ (suc zero)) (there here) 700))))

seal-name-example : Term
seal-name-example =
  ((inst
     (inst
       (Kdyn down (ν (ν (tag (｀ (suc zero)) ↦ (tag (｀ zero) ↦ untag (｀ (suc zero)) 700)))))
       (‵ `ℕ)
       (`∀ (＇ (suc zero) ⇒ ＇ zero ⇒ ＇ (suc zero))))
     (‵ `ℕ)
     ((‵ `ℕ) ⇒ ＇ zero ⇒ (‵ `ℕ)))
    · nat 42)
   · nat 0

seal-name-example-⊢ : 0 ∣ 0 ∣ [] ∣ [] ⊢ seal-name-example ⦂ (‵ `ℕ)
seal-name-example-⊢ =
  ⊢·
    (⊢·
      (inst-wt
        _
        (‵ `ℕ)
        ((‵ `ℕ) ⇒ ＇ zero ⇒ (‵ `ℕ))
        (inst-wt
          _
          (‵ `ℕ)
          (`∀ (＇ (suc zero) ⇒ ＇ zero ⇒ ＇ (suc zero)))
          (⊢down Kdyn-⊢ kDyn-to-∀X-∀Y-X⇒Y⇒X)
          wfBase)
        wfBase)
      n42-⊢)
    (nat-⊢ 0)

seal-name-example-test : evalNat uniq[] gas seal-name-example-⊢ ≡ just 42
seal-name-example-test = refl

seal-name-example-trace :
  Σ[ Ψ′ ∈ SealCtx ]
  Σ[ Σ′ ∈ Store ]
  Σ[ N ∈ Term ]
  Σ[ A′ ∈ Ty ]
  Σ[ N⊢ ∈ (0 ∣ Ψ′ ∣ Σ′ ∣ [] ⊢ N ⦂ A′) ]
    ([] ∣ seal-name-example —↠ Σ′ ∣ N)
seal-name-example-trace = eval uniq[] gas seal-name-example-⊢

seal-name-example-↠ :
  [] ∣ seal-name-example —↠ ((zero , ‵ `ℕ) ∷ ((suc zero , ‵ `ℕ) ∷ [])) ∣ ($ (κℕ 42))
seal-name-example-↠ =
  seal-name-example
    —→⟨ ξ-·₁ (ξ-·₁ β-ν) ⟩
  (((((ν:= ‵ `ℕ ∙
        ((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (ν (ν (tag (｀ 1) ↦ (tag (｀ 0) ↦ untag (｀ 1) 700))))
            ) • 0)
          up (∀ᵖ (seal 0 ↦ (id ↦ unseal 0)))))
      • 0)
     up (id ↦ (seal 0 ↦ id)))
    · ($ (κℕ 42)))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-·₁ (ξ-up (ξ-·α β-ν))) ⟩
  ((((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (ν (ν (tag (｀ 1) ↦ (tag (｀ 0) ↦ untag (｀ 1) 700))))
        ) • 0)
      up (∀ᵖ (seal 0 ↦ (id ↦ unseal 0))))
     • 1)
    up (id ↦ (seal 1 ↦ id)))
   · ($ (κℕ 42)))
  · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-·₁ (ξ-up (ξ-·α (ξ-up (id-step β-down-ν))))) ⟩
  (((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (ν (tag (｀ 1) ↦ (tag (｀ 0) ↦ untag (｀ 1) 700)))
      ) up (∀ᵖ (seal 0 ↦ (id ↦ unseal 0))))
     • 1)
    up (id ↦ (seal 1 ↦ id)))
   · ($ (κℕ 42)))
  · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-·₁ (ξ-up (id-step β-up-∀))) ⟩
  (((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (ν (tag (｀ 1) ↦ (tag (｀ 0) ↦ untag (｀ 1) 700)))
      ) • 1)
    up (seal 0 ↦ (id ↦ unseal 0)))
   up (id ↦ (seal 1 ↦ id)))
  · ($ (κℕ 42)))
 · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-·₁ (ξ-up (ξ-up (id-step β-down-ν)))) ⟩
  ((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (tag (｀ 0) ↦ (tag (｀ 1) ↦ untag (｀ 0) 700)))
      up (seal 0 ↦ (id ↦ unseal 0)))
     up (id ↦ (seal 1 ↦ id)))
    · ($ (κℕ 42)))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (id-step β-up-↦) ⟩
  ((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (tag (｀ 0) ↦ (tag (｀ 1) ↦ untag (｀ 0) 700)))
      up (seal 0 ↦ (id ↦ unseal 0)))
     · (($ (κℕ 42)) down id))
    up (seal 1 ↦ id))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-up (ξ-·₂ (_up_ (_down_ (ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) _↦_) _↦_) (id-step id-down))) ⟩
  ((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (tag (｀ 0) ↦ (tag (｀ 1) ↦ untag (｀ 0) 700)))
      up (seal 0 ↦ (id ↦ unseal 0)))
     · ($ (κℕ 42)))
    up (seal 1 ↦ id))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-up (id-step β-up-↦)) ⟩
  ((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1)) down (tag (｀ 0) ↦ (tag (｀ 1) ↦ untag (｀ 0) 700)))
      · (($ (κℕ 42)) down seal 0))
     up (id ↦ unseal 0))
    up (seal 1 ↦ id))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-up (ξ-up (id-step β-down-↦))) ⟩
  ((((((ƛ ★ ⇒ (ƛ ★ ⇒ ` 1))
       · ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      down (tag (｀ 1) ↦ untag (｀ 0) 700))
     up (id ↦ unseal 0))
    up (seal 1 ↦ id))
   · ($ (κℕ 0)))
    —→⟨ ξ-·₁ (ξ-up (ξ-up (ξ-down (id-step (β (_up_ (_down_ ($ (κℕ 42)) seal) tag)))))) ⟩
  (((((ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      down (tag (｀ 1) ↦ untag (｀ 0) 700))
     up (id ↦ unseal 0))
    up (seal 1 ↦ id))
   · ($ (κℕ 0)))
    —→⟨ id-step β-up-↦ ⟩
  (((((ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      down (tag (｀ 1) ↦ untag (｀ 0) 700))
     up (id ↦ unseal 0))
    · (($ (κℕ 0)) down seal 1))
   up id)
    —→⟨ ξ-up (id-step β-up-↦) ⟩
  (((((ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      down (tag (｀ 1) ↦ untag (｀ 0) 700))
     · ((($ (κℕ 0)) down seal 1) down id))
    up unseal 0)
   up id)
    —→⟨ ξ-up (ξ-up (ξ-·₂ (_down_ (ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0))) _↦_) (id-step id-down))) ⟩
  (((((ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      down (tag (｀ 1) ↦ untag (｀ 0) 700))
     · (($ (κℕ 0)) down seal 1))
    up unseal 0)
   up id)
    —→⟨ ξ-up (ξ-up (id-step β-down-↦)) ⟩
  (((((ƛ ★ ⇒ ((($ (κℕ 42)) down seal 0) up tag (｀ 0)))
      · ((($ (κℕ 0)) down seal 1) up tag (｀ 1)))
     down untag (｀ 0) 700)
    up unseal 0)
   up id)
    —→⟨ ξ-up (ξ-up (ξ-down (id-step (β (_up_ (_down_ ($ (κℕ 0)) seal) tag))))) ⟩
  (((((($ (κℕ 42)) down seal 0) up tag (｀ 0))
     down untag (｀ 0) 700)
    up unseal 0)
   up id)
    —→⟨ ξ-up (ξ-up (id-step tag-untag-ok)) ⟩
  (((($ (κℕ 42)) down seal 0) up unseal 0) up id)
    —→⟨ ξ-up (id-step seal-unseal) ⟩
  (($ (κℕ 42)) up id)
    —→⟨ id-step id-up ⟩
  ($ (κℕ 42)) ∎
