module NuExamplesFresh where

-- File Charter:
--   * Closed NuTerms examples that exercise the Maybe-based type checker.
--   * Adapted from the PolyUpDown extrinsic-inst fresh examples, but limited
--     to typing regressions because the NuTerms evaluator is not in place.
--   * Covers base/dynamic casts, unannotated lambdas under expected types,
--     polymorphic `ν` instantiation, and representative rejection cases.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import TypeCheck using (IsJust; fromJust; is-just; type-check-expect)

------------------------------------------------------------------------
-- Shared terms and helpers
------------------------------------------------------------------------

Nat : Ty
Nat = ‵ `ℕ

BoolTy : Ty
BoolTy = ‵ `𝔹

expect-⊢ :
  (M : Term) →
  (A : Ty) →
  IsJust (type-check-expect 0 [] [] M A) →
  0 ∣ [] ∣ [] ⊢ M ⦂ A
expect-⊢ M A ok = fromJust (type-check-expect 0 [] [] M A) ok

nat : ℕ → Term
nat n = $ (κℕ n)

c : Term
c = nat 7

n42 : Term
n42 = nat 42

n69 : Term
n69 = nat 69

tagNat : Coercion
tagNat = id Nat ︔ (Nat !)

untagNat : Coercion
untagNat = Nat ？

tagBool : Coercion
tagBool = id BoolTy ︔ (BoolTy !)

untagBool : Coercion
untagBool = BoolTy ？

nat★ : ℕ → Term
nat★ n = nat n ⟨ tagNat ⟩

c★ : Term
c★ = nat★ 7

n42★ : Term
n42★ = nat★ 42

n69★ : Term
n69★ = nat★ 69

idDyn : Term
idDyn = ƛ (` 0)

natId : Term
natId = ƛ (` 0)

Kdyn : Term
Kdyn = ƛ (ƛ (` 1))

idFun★ : Term
idFun★ = idDyn ⟨ id (★ ⇒ ★) ︔ ((★ ⇒ ★) !) ⟩

polyId : Term
polyId = Λ (ƛ (` 0))

polyK : Term
polyK = Λ (ƛ (ƛ (` 1)))

polyBetaId : Term
polyBetaId = Λ (ƛ ((ƛ (` 0)) · (` 0)))

sealNatId : Coercion
sealNatId = seal Nat 0 ↦ unseal 0 Nat

sealDynId : Coercion
sealDynId = seal ★ 0 ↦ unseal 0 ★

sealNatK : Coercion
sealNatK = seal Nat 0 ↦ (seal Nat 0 ↦ unseal 0 Nat)

sealDynK : Coercion
sealDynK = seal ★ 0 ↦ (seal ★ 0 ↦ unseal 0 ★)

polyIdNat : Term
polyIdNat = ν Nat polyId sealNatId

polyIdDyn : Term
polyIdDyn = ν ★ polyId sealDynId

polyKNat : Term
polyKNat = ν Nat polyK sealNatK

polyKDyn : Term
polyKDyn = ν ★ polyK sealDynK

------------------------------------------------------------------------
-- Shared typing checks
------------------------------------------------------------------------

c-⊢ : 0 ∣ [] ∣ [] ⊢ c ⦂ Nat
c-⊢ = expect-⊢ c Nat is-just

c★-⊢ : 0 ∣ [] ∣ [] ⊢ c★ ⦂ ★
c★-⊢ = expect-⊢ c★ ★ is-just

idDyn-⊢ : 0 ∣ [] ∣ [] ⊢ idDyn ⦂ ★ ⇒ ★
idDyn-⊢ = expect-⊢ idDyn (★ ⇒ ★) is-just

natId-⊢ : 0 ∣ [] ∣ [] ⊢ natId ⦂ Nat ⇒ Nat
natId-⊢ = expect-⊢ natId (Nat ⇒ Nat) is-just

Kdyn-⊢ : 0 ∣ [] ∣ [] ⊢ Kdyn ⦂ ★ ⇒ ★ ⇒ ★
Kdyn-⊢ = expect-⊢ Kdyn (★ ⇒ ★ ⇒ ★) is-just

idFun★-⊢ : 0 ∣ [] ∣ [] ⊢ idFun★ ⦂ ★
idFun★-⊢ = expect-⊢ idFun★ ★ is-just

polyId-⊢ : 0 ∣ [] ∣ [] ⊢ polyId ⦂ `∀ (＇ 0 ⇒ ＇ 0)
polyId-⊢ = expect-⊢ polyId (`∀ (＇ 0 ⇒ ＇ 0)) is-just

polyK-⊢ : 0 ∣ [] ∣ [] ⊢ polyK ⦂ `∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0)
polyK-⊢ = expect-⊢ polyK (`∀ (＇ 0 ⇒ ＇ 0 ⇒ ＇ 0)) is-just

------------------------------------------------------------------------
-- Example 1
------------------------------------------------------------------------

example1-left : Term
example1-left = (idDyn · c★) ⟨ untagNat ⟩

example1-left-⊢ : 0 ∣ [] ∣ [] ⊢ example1-left ⦂ Nat
example1-left-⊢ = expect-⊢ example1-left Nat is-just

example1-right : Term
example1-right = idDyn · c★

example1-right-⊢ : 0 ∣ [] ∣ [] ⊢ example1-right ⦂ ★
example1-right-⊢ = expect-⊢ example1-right ★ is-just

------------------------------------------------------------------------
-- Example 5: cast up then down
------------------------------------------------------------------------

example5-left : Term
example5-left = example1-left

example5-left-⊢ : 0 ∣ [] ∣ [] ⊢ example5-left ⦂ Nat
example5-left-⊢ = expect-⊢ example5-left Nat is-just

example5-right : Term
example5-right = (example1-left ⟨ tagNat ⟩) ⟨ untagNat ⟩

example5-right-⊢ : 0 ∣ [] ∣ [] ⊢ example5-right ⦂ Nat
example5-right-⊢ = expect-⊢ example5-right Nat is-just

------------------------------------------------------------------------
-- Example 6: down then up
------------------------------------------------------------------------

example6-right : Term
example6-right = (example1-right ⟨ untagNat ⟩) ⟨ tagNat ⟩

example6-right-⊢ : 0 ∣ [] ∣ [] ⊢ example6-right ⦂ ★
example6-right-⊢ = expect-⊢ example6-right ★ is-just

------------------------------------------------------------------------
-- Example 9: constant function
------------------------------------------------------------------------

example9-left : Term
example9-left = ((Kdyn · n42★) · n69★) ⟨ untagNat ⟩

example9-left-⊢ : 0 ∣ [] ∣ [] ⊢ example9-left ⦂ Nat
example9-left-⊢ = expect-⊢ example9-left Nat is-just

example9-right : Term
example9-right = (Kdyn · n42★) · n69★

example9-right-⊢ : 0 ∣ [] ∣ [] ⊢ example9-right ⦂ ★
example9-right-⊢ = expect-⊢ example9-right ★ is-just

------------------------------------------------------------------------
-- Polymorphic instantiation via `ν`
------------------------------------------------------------------------

polyIdNat-⊢ : 0 ∣ [] ∣ [] ⊢ polyIdNat ⦂ Nat ⇒ Nat
polyIdNat-⊢ = expect-⊢ polyIdNat (Nat ⇒ Nat) is-just

polyIdNat-app : Term
polyIdNat-app = polyIdNat · c

polyIdNat-app-⊢ : 0 ∣ [] ∣ [] ⊢ polyIdNat-app ⦂ Nat
polyIdNat-app-⊢ = expect-⊢ polyIdNat-app Nat is-just

polyIdDyn-⊢ : 0 ∣ [] ∣ [] ⊢ polyIdDyn ⦂ ★ ⇒ ★
polyIdDyn-⊢ = expect-⊢ polyIdDyn (★ ⇒ ★) is-just

polyIdDyn-app : Term
polyIdDyn-app = polyIdDyn · c★

polyIdDyn-app-⊢ : 0 ∣ [] ∣ [] ⊢ polyIdDyn-app ⦂ ★
polyIdDyn-app-⊢ = expect-⊢ polyIdDyn-app ★ is-just

sec5-β : Term
sec5-β = (ν Nat polyBetaId sealNatId) · c

sec5-β-⊢ : 0 ∣ [] ∣ [] ⊢ sec5-β ⦂ Nat
sec5-β-⊢ = expect-⊢ sec5-β Nat is-just

sec6-K-dyn : Term
sec6-K-dyn = (polyKDyn · n42★) · n69★

sec6-K-dyn-⊢ : 0 ∣ [] ∣ [] ⊢ sec6-K-dyn ⦂ ★
sec6-K-dyn-⊢ = expect-⊢ sec6-K-dyn ★ is-just

sec6-K-base : Term
sec6-K-base = (polyKNat · n42) · n69

sec6-K-base-⊢ : 0 ∣ [] ∣ [] ⊢ sec6-K-base ⦂ Nat
sec6-K-base-⊢ = expect-⊢ sec6-K-base Nat is-just

------------------------------------------------------------------------
-- Rejection checks
------------------------------------------------------------------------

bad-nat-as-dyn : type-check-expect 0 [] [] c ★ ≡ nothing
bad-nat-as-dyn = refl

bad-ground-mismatch :
  type-check-expect 0 [] [] (c★ ⟨ untagBool ⟩) Nat ≡ nothing
bad-ground-mismatch = refl

bad-application : type-check-expect 0 [] [] (c · c) Nat ≡ nothing
bad-application = refl
