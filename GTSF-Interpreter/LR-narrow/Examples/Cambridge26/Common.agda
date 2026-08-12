module LR-narrow.Examples.Cambridge26.Common where

-- File Charter:
--   * Defines the shared closed programs, coercions, and imprecision indices
--     used by the Cambridge26 LR regression specifications.
--   * Uses `ν` directly for compiled System-F type application.
--   * Contains no reduction trace or term-imprecision proof.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; z<s; s<s)

open import Coercions hiding (id)
import ImprecisionWf as IW
open import ImprecisionWf hiding (id★)
open import NuTerms
open import Primitives using (κℕ)
open import Types

Nat : Ty
Nat = ‵ `ℕ

Bool : Ty
Bool = ‵ `𝔹

X₁ : Ty
X₁ = ＇ 1

IdBody : Ty
IdBody = X₀ ⇒ X₀

PolyId : Ty
PolyId = `∀ IdBody

DynId : Ty
DynId = ★ ⇒ ★

KBody : Ty
KBody = `∀ (X₁ ⇒ X₀ ⇒ X₁)

PolyK : Ty
PolyK = `∀ KBody

DynK : Ty
DynK = ★ ⇒ ★ ⇒ ★

nat : ℕ → Term
nat n = $ (κℕ n)

nat★ : ℕ → Term
nat★ n = nat n ⟨ Nat ! ⟩

id★ : Term
id★ = ƛ (` zero)

j : Term
j = ƛ (nat★ 0)

id : Term
id = Λ (ƛ (` zero))

wrong-ground-argument : Term
wrong-ground-argument = id★ ⟨ DynId ! ⟩

nat-function-to-dynamic-cast : Coercion
nat-function-to-dynamic-cast = (Nat ？) ↦ (Nat !)

as-dynamic-nat-function : Term → Term
as-dynamic-nat-function M = M ⟨ nat-function-to-dynamic-cast ⟩

k★ : Term
k★ = ƛ (ƛ (` 1))

k : Term
k = Λ (Λ (ƛ (ƛ (` 1))))

var-id-narrowing : Coercion
var-id-narrowing = (X₀ !) ↦ (X₀ ？)

id-generalization : Coercion
id-generalization = gen DynId var-id-narrowing

id-instantiation : Coercion
id-instantiation =
  inst DynId ((seal ★ zero) ↦ (unseal zero ★))

generalize-id : Term → Term
generalize-id M = M ⟨ id-generalization ⟩

instantiate-id-dynamically : Term → Term
instantiate-id-dynamically M = M ⟨ id-instantiation ⟩

round-trip-id : Term → Term
round-trip-id M = generalize-id (instantiate-id-dynamically M)

two-round-trips-id : Term → Term
two-round-trips-id M = round-trip-id (round-trip-id M)

instantiate-at : Ty → Ty → Term → Term
instantiate-at body A M =
  ν A M (reveal body zero (⇑ᵗ A))

id-at : Ty → Term
id-at A = instantiate-at IdBody A id

k-at-from : Ty → Ty → Term → Term
k-at-from A B M =
  instantiate-at (⇑ᵗ A ⇒ X₀ ⇒ ⇑ᵗ A) B
    (instantiate-at KBody A M)

k-at : Ty → Ty → Term
k-at A B = k-at-from A B k

k-instantiation : Coercion
k-instantiation =
  inst DynK
    (inst DynK
      ((seal ★ 1) ↦ ((seal ★ zero) ↦ (unseal 1 ★))))

k-generalization : Coercion
k-generalization =
  gen DynK
    (gen DynK
      ((X₁ !) ↦ ((X₀ !) ↦ (X₁ ？))))

instantiate-k-dynamically : Term → Term
instantiate-k-dynamically M = M ⟨ k-instantiation ⟩

generalize-k : Term → Term
generalize-k M = M ⟨ k-generalization ⟩

rebinding-id : Term
rebinding-id =
  Λ (ƛ (instantiate-at IdBody X₀ id · (` zero)))

dynamic-id :
  [] ∣ zero ⊢ DynId ⊑ DynId ⊣ zero
dynamic-id = IW.id★ ↦ IW.id★

dynamic-result :
  [] ∣ zero ⊢ ★ ⊑ ★ ⊣ zero
dynamic-result = IW.id★

nat-reflexive :
  [] ∣ zero ⊢ Nat ⊑ Nat ⊣ zero
nat-reflexive = idι

nat-id :
  [] ∣ zero ⊢ Nat ⇒ Nat ⊑ Nat ⇒ Nat ⊣ zero
nat-id = idι ↦ idι

nat-to-dynamic :
  [] ∣ zero ⊢ Nat ⊑ ★ ⊣ zero
nat-to-dynamic = tag `ℕ

nat-function-to-dynamic :
  [] ∣ zero ⊢ Nat ⇒ Nat ⊑ DynId ⊣ zero
nat-function-to-dynamic = (tag `ℕ) ↦ (tag `ℕ)

poly-id-to-dynamic :
  [] ∣ zero ⊢ PolyId ⊑ DynId ⊣ zero
poly-id-to-dynamic =
  ν nonvar-fun refl
    ((tagˣ (here refl) z<s) ↦ (tagˣ (here refl) z<s))

poly-id-reflexive :
  [] ∣ zero ⊢ PolyId ⊑ PolyId ⊣ zero
poly-id-reflexive =
  ∀ⁱ ((idˣ (here refl) z<s z<s) ↦
      (idˣ (here refl) z<s z<s))

poly-k-to-dynamic :
  [] ∣ zero ⊢ PolyK ⊑ DynK ⊣ zero
poly-k-to-dynamic =
  ν nonvar-all refl
    (ν nonvar-fun refl
      ((tagˣ (there (here refl)) (s<s z<s)) ↦
        ((tagˣ (here refl) z<s) ↦
          (tagˣ (there (here refl)) (s<s z<s)))))

poly-k-reflexive :
  [] ∣ zero ⊢ PolyK ⊑ PolyK ⊣ zero
poly-k-reflexive =
  ∀ⁱ (∀ⁱ
    ((idˣ (there (here refl)) (s<s z<s) (s<s z<s)) ↦
      ((idˣ (here refl) z<s z<s) ↦
        (idˣ (there (here refl)) (s<s z<s) (s<s z<s)))))

poly-k-to-dynamic-first :
  [] ∣ zero ⊢ PolyK ⊑ `∀ (★ ⇒ X₀ ⇒ ★) ⊣ zero
poly-k-to-dynamic-first =
  ν nonvar-all refl
    (∀ⁱ
      ((tagˣ (there (here refl)) (s<s z<s)) ↦
        ((idˣ (here refl) z<s z<s) ↦
          (tagˣ (there (here refl)) (s<s z<s)))))

poly-k-to-dynamic-second :
  [] ∣ zero ⊢ PolyK ⊑ `∀ (X₀ ⇒ ★ ⇒ X₀) ⊣ zero
poly-k-to-dynamic-second =
  ∀ⁱ
    (ν nonvar-fun refl
      ((idˣ (there (here refl)) (s<s z<s) z<s) ↦
        ((tagˣ (here refl) z<s) ↦
          (idˣ (there (here refl)) (s<s z<s) z<s))))
