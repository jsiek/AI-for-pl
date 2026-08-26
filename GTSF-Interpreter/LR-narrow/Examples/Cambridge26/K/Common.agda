module LR-narrow.Examples.Cambridge26.K.Common where

-- File Charter:
--   * Defines the four precision vertices for polymorphic K and the casts
--     that independently instantiate/generalize its `X` and `Y` binders.
--   * Defines the corresponding live type-imprecision derivations.
--   * Contains no logical-relation proof or small-step dependency.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (zero; z<s)

open import Coercions
import ImprecisionWf as IW
open import ImprecisionWf hiding (id★)
open import LR-narrow.Examples.Cambridge26.Common hiding (id)
open import NuTerms
open import Types

X-dynamic-K : Ty
X-dynamic-K = `∀ (★ ⇒ X₀ ⇒ ★)

Y-dynamic-K : Ty
Y-dynamic-K = `∀ (X₀ ⇒ ★ ⇒ X₀)

K-X-dynamic : Term
K-X-dynamic = Λ (ƛ (ƛ (` 1)))

K-Y-dynamic : Term
K-Y-dynamic = Λ (ƛ (ƛ (` 1)))

instantiate-X-with-Y-polymorphic : Coercion
instantiate-X-with-Y-polymorphic =
  inst X-dynamic-K
    (`∀ ((seal ★ 1) ↦ ((id X₀) ↦ (unseal 1 ★))))

generalize-X-with-Y-polymorphic : Coercion
generalize-X-with-Y-polymorphic =
  gen X-dynamic-K
    (`∀ ((X₁ !) ↦ ((id X₀) ↦ (X₁ ？))))

instantiate-Y-under-X : Coercion
instantiate-Y-under-X =
  `∀ (inst (X₀ ⇒ ★ ⇒ X₀)
    ((id X₁) ↦ ((seal ★ zero) ↦ (id X₁))))

generalize-Y-under-X : Coercion
generalize-Y-under-X =
  `∀ (gen (X₀ ⇒ ★ ⇒ X₀)
    ((id X₁) ↦ ((X₀ !) ↦ (id X₁))))

instantiate-Y-with-X-dynamic : Coercion
instantiate-Y-with-X-dynamic =
  inst DynK ((id ★) ↦ ((seal ★ zero) ↦ (id ★)))

generalize-Y-with-X-dynamic : Coercion
generalize-Y-with-X-dynamic =
  gen DynK ((id ★) ↦ ((X₀ !) ↦ (id ★)))

instantiate-X-with-Y-dynamic : Coercion
instantiate-X-with-Y-dynamic =
  inst DynK ((seal ★ zero) ↦ ((id ★) ↦ (unseal zero ★)))

generalize-X-with-Y-dynamic : Coercion
generalize-X-with-Y-dynamic =
  gen DynK ((X₀ !) ↦ ((id ★) ↦ (X₀ ？)))

instantiate-X : Term → Term
instantiate-X M = M ⟨ instantiate-X-with-Y-polymorphic ⟩

generalize-X : Term → Term
generalize-X M = M ⟨ generalize-X-with-Y-polymorphic ⟩

instantiate-Y : Term → Term
instantiate-Y M = M ⟨ instantiate-Y-under-X ⟩

generalize-Y : Term → Term
generalize-Y M = M ⟨ generalize-Y-under-X ⟩

instantiate-Y-after-X : Term → Term
instantiate-Y-after-X M = M ⟨ instantiate-Y-with-X-dynamic ⟩

generalize-Y-after-X : Term → Term
generalize-Y-after-X M = M ⟨ generalize-Y-with-X-dynamic ⟩

instantiate-X-after-Y : Term → Term
instantiate-X-after-Y M = M ⟨ instantiate-X-with-Y-dynamic ⟩

generalize-X-after-Y : Term → Term
generalize-X-after-Y M = M ⟨ generalize-X-with-Y-dynamic ⟩

X-dynamic-to-dynamic :
  [] ∣ zero ⊢ X-dynamic-K ⊑ DynK ⊣ zero
X-dynamic-to-dynamic =
  ν nonvar-fun refl
    (IW.id★ ↦ ((tagˣ (here refl) z<s) ↦ IW.id★))

Y-dynamic-to-dynamic :
  [] ∣ zero ⊢ Y-dynamic-K ⊑ DynK ⊣ zero
Y-dynamic-to-dynamic =
  ν nonvar-fun refl
    ((tagˣ (here refl) z<s) ↦ (IW.id★ ↦
      (tagˣ (here refl) z<s)))

X-dynamic-reflexive :
  [] ∣ zero ⊢ X-dynamic-K ⊑ X-dynamic-K ⊣ zero
X-dynamic-reflexive =
  ∀ⁱ (IW.id★ ↦ ((idˣ (here refl) z<s z<s) ↦ IW.id★))

Y-dynamic-reflexive :
  [] ∣ zero ⊢ Y-dynamic-K ⊑ Y-dynamic-K ⊣ zero
Y-dynamic-reflexive =
  ∀ⁱ ((idˣ (here refl) z<s z<s) ↦ (IW.id★ ↦
    (idˣ (here refl) z<s z<s)))

dynamic-K-reflexive :
  [] ∣ zero ⊢ DynK ⊑ DynK ⊣ zero
dynamic-K-reflexive = IW.id★ ↦ (IW.id★ ↦ IW.id★)
