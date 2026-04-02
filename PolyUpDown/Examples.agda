module Examples where

-- File Charter:
--   * Closed example terms for PolyUpDown together with small evaluation tests.
--   * Regression checks that the dynamic semantics still computes the intended
--     results on representative casts and polymorphic examples.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
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

polyId : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ (＇ Zᵗ ⇒ ＇ Zᵗ))
polyId = Λ (ƛ (＇ Zᵗ) ⇒ ` Z)

idDyn : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (★ ⇒ ★)
idDyn = ƛ ★ ⇒ ` Z

nat : ∀ {Ψ}{Σ : Store 0 Ψ} → ℕ → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)
nat n = $ (κℕ n) refl

nat★ : ∀ {Ψ}{Σ : Store 0 Ψ} → ℕ → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★
nat★ n = nat n at[ up ] (tag (‵ `ℕ) tt)

c : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)
c = nat 7

n42 : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)
n42 = nat 42

n69 : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ)
n69 = nat 69

c★ : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★
c★ = nat★ 7

n42★ : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★
n42★ = nat★ 42

n69★ : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★
n69★ = nat★ 69

natId : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (‵ `ℕ ⇒ ‵ `ℕ)
natId = ƛ (‵ `ℕ) ⇒ ` Z

idFun★ : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ ★
idFun★ = idDyn at[ up ] (tag ★⇒★ tt)

polyApp :
  ∀ {Ψ}{Σ : Store 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢
    (`∀ (`∀ (((＇ (Sᵗ Zᵗ)) ⇒ (＇ Zᵗ)) ⇒ ((＇ (Sᵗ Zᵗ)) ⇒ (＇ Zᵗ)))))
polyApp =
  Λ
    (Λ
      (ƛ ((＇ (Sᵗ Zᵗ)) ⇒ (＇ Zᵗ)) ⇒
        ƛ (＇ (Sᵗ Zᵗ)) ⇒
          (` (S Z) · ` Z)))

polyK : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ (＇ Zᵗ ⇒ ＇ Zᵗ ⇒ ＇ Zᵗ))
polyK = Λ (ƛ (＇ Zᵗ) ⇒ ƛ (＇ Zᵗ) ⇒ ` (S Z))

polyBetaId : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (`∀ (＇ Zᵗ ⇒ ＇ Zᵗ))
polyBetaId =
  Λ
    (ƛ (＇ Zᵗ) ⇒
      ((ƛ (＇ Zᵗ) ⇒ ` Z) · ` Z))

kDyn-to-nat★nat :
  ∀ {Ψ}{Σ : Store 0 Ψ} →
  Label →
  Σ ∣ every Ψ ∣ every Ψ ⊢ (★ ⇒ ★ ⇒ ★) ⊒ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
kDyn-to-nat★nat ℓ = tag (‵ `ℕ) tt ↦ (id ↦ untag (‵ `ℕ) tt ℓ)

kNat-to-nat★nat :
  ∀ {Ψ}{Σ : Store 0 Ψ} →
  Label →
  Σ ∣ every Ψ ∣ every Ψ ⊢ (‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ) ⊑ (‵ `ℕ ⇒ ★ ⇒ ‵ `ℕ)
kNat-to-nat★nat ℓ = id ↦ (untag (‵ `ℕ) tt ℓ ↦ id)

idDyn-to-∀X-X⇒★ :
  ∀ {Ψ}{Σ : Store 0 Ψ} →
  Σ ∣ every Ψ ∣ every Ψ ⊢ (★ ⇒ ★) ⊒ (`∀ (＇ Zᵗ ⇒ ★))
idDyn-to-∀X-X⇒★ = ν (tag (｀ Zˢ) (every-member Zˢ) ↦ id)

gas : ℕ
gas = 250

isNatValue :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  Maybe ℕ
isNatValue ($ (κℕ n) _) = just n
isNatValue _ = nothing

isNatDynValue :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  Maybe ℕ
isNatDynValue (($ (κℕ n) _) at[ d ] p) = just n
isNatDynValue _ = nothing

isBlameValue :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  0 ∣ Ψ ∣ Σ ∣ [] ⊢ A →
  Maybe Label
isBlameValue (blame ℓ) = just ℓ
isBlameValue _ = nothing

evalNat :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  Maybe ℕ
evalNat uΣ fuel M with eval uΣ fuel M
... | _ , _ , _ , N , _ = isNatValue N

evalNatDyn :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  Maybe ℕ
evalNatDyn uΣ fuel M with eval uΣ fuel M
... | _ , _ , _ , N , _ = isNatDynValue N

evalBlame :
  ∀ {Ψ}{Σ : Store 0 Ψ}{A : Ty 0 Ψ} →
  Uniqueˢ Σ →
  (fuel : ℕ) →
  (M : 0 ∣ Ψ ∣ Σ ∣ [] ⊢ A) →
  Maybe Label
evalBlame uΣ fuel M with eval uΣ fuel M
... | _ , _ , _ , N , _ = isBlameValue N

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

example1-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example1-left = (idDyn · c★) at[ down ] (untag (‵ `ℕ) tt 1)

example1-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example1-right = idDyn · c★

example1-left-test : evalNat uniq[] gas example1-left ≡ just 7
example1-left-test = refl

example1-right-test : evalNatDyn uniq[] gas example1-right ≡ just 7
example1-right-test = refl

------------------------------------------------------------------------
-- Example 2
------------------------------------------------------------------------

example2-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example2-left = example1-left

example2-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example2-right = idDyn · c★

example2-left-test : evalNat uniq[] gas example2-left ≡ just 7
example2-left-test = refl

example2-right-test : evalNatDyn uniq[] gas example2-right ≡ just 7
example2-right-test = refl

------------------------------------------------------------------------
-- Example 3
------------------------------------------------------------------------

example3-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example3-left = idDyn · c★

example3-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example3-right = idDyn · c★

example3-left-test : evalNatDyn uniq[] gas example3-left ≡ just 7
example3-left-test = refl

example3-right-test : evalNatDyn uniq[] gas example3-right ≡ just 7
example3-right-test = refl

------------------------------------------------------------------------
-- Example 4
------------------------------------------------------------------------

example4-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example4-left = example1-left

example4-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example4-right = example3-left

example4-left-test : evalNat uniq[] gas example4-left ≡ just 7
example4-left-test = refl

example4-right-test : evalNatDyn uniq[] gas example4-right ≡ just 7
example4-right-test = refl

------------------------------------------------------------------------
-- Example 5 (cast up then down)
------------------------------------------------------------------------

example5-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example5-left = example1-left

example5-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example5-right =
  (example1-left at[ up ] (tag (‵ `ℕ) tt)) at[ down ] (untag (‵ `ℕ) tt 5)

example5-left-test : evalNat uniq[] gas example5-left ≡ just 7
example5-left-test = refl

example5-right-test : evalNat uniq[] gas example5-right ≡ just 7
example5-right-test = refl

------------------------------------------------------------------------
-- Example 6 (up, down, up)
------------------------------------------------------------------------

example6-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example6-left = example1-left

example6-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example6-right =
  (example1-right at[ down ] (untag (‵ `ℕ) tt 6)) at[ up ] (tag (‵ `ℕ) tt)

example6-left-test : evalNat uniq[] gas example6-left ≡ just 7
example6-left-test = refl

example6-right-test : evalNatDyn uniq[] gas example6-right ≡ just 7
example6-right-test = refl

------------------------------------------------------------------------
-- Example 7 (up, down, up, down)
------------------------------------------------------------------------

example7-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example7-left = example1-left

example7-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example7-right =
  (example5-right at[ up ] (tag (‵ `ℕ) tt)) at[ down ] (untag (‵ `ℕ) tt 7)

example7-left-test : evalNat uniq[] gas example7-left ≡ just 7
example7-left-test = refl

example7-right-test : evalNat uniq[] gas example7-right ≡ just 7
example7-right-test = refl

------------------------------------------------------------------------
-- Example 8 (cast down on the right)
------------------------------------------------------------------------

example8-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example8-left = example1-left

example8-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example8-right = example1-left at[ down ] id

example8-left-test : evalNat uniq[] gas example8-left ≡ just 7
example8-left-test = refl

example8-right-test : evalNat uniq[] gas example8-right ≡ just 7
example8-right-test = refl

------------------------------------------------------------------------
-- Example 9 (constant function)
------------------------------------------------------------------------

Kdyn : ∀ {Ψ}{Σ : Store 0 Ψ} → 0 ∣ Ψ ∣ Σ ∣ [] ⊢ (★ ⇒ ★ ⇒ ★)
Kdyn = ƛ ★ ⇒ ƛ ★ ⇒ ` (S Z)

example9-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example9-left = ((Kdyn · n42★) · n69★) at[ down ] (untag (‵ `ℕ) tt 9)

example9-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example9-right = (Kdyn · n42★) · n69★

example9-left-test : evalNat uniq[] gas example9-left ≡ just 42
example9-left-test = refl

example9-right-test : evalNatDyn uniq[] gas example9-right ≡ just 42
example9-right-test = refl

------------------------------------------------------------------------
-- Example 10 (constant function, cast wrapper on right)
------------------------------------------------------------------------

example10-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example10-left = example9-left

example10-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example10-right = ((Kdyn at[ up ] id) · n42★) · n69★

example10-left-test : evalNat uniq[] gas example10-left ≡ just 42
example10-left-test = refl

example10-right-test : evalNatDyn uniq[] gas example10-right ≡ just 42
example10-right-test = refl

------------------------------------------------------------------------
-- Example 11 (nested ν)
------------------------------------------------------------------------

example11-left : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example11-left =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙ c)

example11-right : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
example11-right = (ƛ ★ ⇒ ((ƛ ★ ⇒ ` Z) · ` Z)) · c★

example11-left-test : evalNat uniq[] gas example11-left ≡ just 7
example11-left-test = refl

example11-right-test : evalNatDyn uniq[] gas example11-right ≡ just 7
example11-right-test = refl

------------------------------------------------------------------------
-- Example 12
------------------------------------------------------------------------

example12 : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example12 =
  ((c★ at[ down ] (untag (‵ `ℕ) tt 12))
   at[ up ] (tag (‵ `ℕ) tt))
  at[ down ] (untag (‵ `ℕ) tt 12)

example12-test : evalNat uniq[] gas example12 ≡ just 7
example12-test = refl

------------------------------------------------------------------------
-- Example 13 (same tag succeeds, mixed tag blames)
------------------------------------------------------------------------

example13-good : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
example13-good =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙
      (((c★ at[ down ] (untag (‵ `ℕ) tt 13))
        at[ up ] (tag (‵ `ℕ) tt))
       at[ down ] (untag (‵ `ℕ) tt 13)))

example13-mixed : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `𝔹)
example13-mixed =
  ν:= ‵ `ℕ ∙
    (ν:= ‵ `ℕ ∙
      (c★ at[ down ] (untag (‵ `𝔹) tt 13)))

example13-good-test : evalNat uniq[] gas example13-good ≡ just 7
example13-good-test = refl

example13-mixed-test : evalBlame uniq[] gas example13-mixed ≡ just 13
example13-mixed-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 2
------------------------------------------------------------------------

sec2-app-dyn : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
sec2-app-dyn = ((inst {A = ★} (inst {A = ★} polyApp)) · idDyn) · c★

sec2-app-base : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
sec2-app-base = ((inst {A = ‵ `ℕ} (inst {A = ‵ `ℕ} polyApp)) · natId) · c

sec2-app-dyn-test : evalNatDyn uniq[] gas sec2-app-dyn ≡ just 7
sec2-app-dyn-test = refl

sec2-app-base-test : evalNat uniq[] gas sec2-app-base ≡ just 7
sec2-app-base-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 5
------------------------------------------------------------------------

sec5-β : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
sec5-β = inst {A = ‵ `ℕ} polyBetaId · c

sec5-β-test : evalNat uniq[] gas sec5-β ≡ just 7
sec5-β-test = refl

------------------------------------------------------------------------
-- Ahmed et al. POPL'11 Section 6
------------------------------------------------------------------------

sec6-K-dyn : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
sec6-K-dyn = ((inst {A = ★} polyK) · n42★) · n69★

sec6-K-base : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
sec6-K-base = ((inst {A = ‵ `ℕ} polyK) · n42) · n69

sec6-K-lax : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
sec6-K-lax =
  ((((inst {A = ★} polyK) at[ down ] kDyn-to-nat★nat 63) · n42) · idFun★)

sec6-K-strict : 0 ∣ 0 ∣ [] ∣ [] ⊢ (‵ `ℕ)
sec6-K-strict =
  ((((inst {A = ‵ `ℕ} polyK) at[ up ] kNat-to-nat★nat 64) · n42) · idFun★)

sec6-id-leak : 0 ∣ 0 ∣ [] ∣ [] ⊢ ★
sec6-id-leak = (inst {A = ‵ `ℕ} (idDyn at[ down ] idDyn-to-∀X-X⇒★)) · n42

sec6-K-dyn-test : evalNatDyn uniq[] gas sec6-K-dyn ≡ just 42
sec6-K-dyn-test = refl

sec6-K-base-test : evalNat uniq[] gas sec6-K-base ≡ just 42
sec6-K-base-test = refl

sec6-K-lax-test : evalNat uniq[] gas sec6-K-lax ≡ just 42
sec6-K-lax-test = refl

sec6-K-strict-test : evalBlame uniq[] gas sec6-K-strict ≡ just 64
sec6-K-strict-test = refl

-- Unlike the POPL'11 calculus, PolyUpDown currently allows this sealed
-- result to escape the surrounding `ν:=`, so evaluation reaches a
-- non-blame result.
sec6-id-leak-test : evalBlame uniq[] gas sec6-id-leak ≡ nothing
sec6-id-leak-test = refl
