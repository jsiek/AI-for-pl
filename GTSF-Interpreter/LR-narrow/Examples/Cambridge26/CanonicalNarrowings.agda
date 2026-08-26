module LR-narrow.Examples.Cambridge26.CanonicalNarrowings where

-- File Charter:
--   * Supplies the small set of checked canonical narrowing derivations used
--     repeatedly by the Cambridge identity and result examples.
--   * Constructs every narrowing explicitly; it does not invoke the compiler.

open import Data.List using ([])
open import Data.Nat using (zero)

open import Coercions
open import LR-narrow.Examples.Cambridge26.CheckedNarrowing
open import LR-narrow.Examples.Cambridge26.Common hiding (id)
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import TypeCheck using (is-just)
open import Types

dynamic-result-c : Coercion
dynamic-result-c = id ★

dynamic-result-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ dynamic-result-c ∶ ★ ⊒ ★
dynamic-result-narrowing = checked-narrowing NW.id★ is-just

nat-reflexive-c : Coercion
nat-reflexive-c = id Nat

nat-reflexive-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ nat-reflexive-c ∶ Nat ⊒ Nat
nat-reflexive-narrowing =
  checked-narrowing (NW.cross (NW.id-‵ `ℕ)) is-just

nat-id-c : Coercion
nat-id-c = id Nat ↦ id Nat

nat-id-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ nat-id-c ∶ Nat ⇒ Nat ⊒ Nat ⇒ Nat
nat-id-narrowing =
  checked-narrowing
    (NW.cross (NW.cross (NW.id-‵ `ℕ) NW.↦
               NW.cross (NW.id-‵ `ℕ)))
    is-just

nat-to-dynamic-c : Coercion
nat-to-dynamic-c = Nat ？

nat-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ nat-to-dynamic-c ∶ ★ ⊒ Nat
nat-to-dynamic-narrowing =
  checked-narrowing (NW.untag (‵ `ℕ)) is-just

nat-function-to-dynamic-c : Coercion
nat-function-to-dynamic-c = (Nat !) ↦ (Nat ？)

nat-function-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ nat-function-to-dynamic-c
    ∶ DynId ⊒ Nat ⇒ Nat
nat-function-to-dynamic-narrowing =
  checked-narrowing
    (NW.cross (NW.tag (‵ `ℕ) NW.↦ NW.untag (‵ `ℕ)))
    is-just

poly-id-to-dynamic-c : Coercion
poly-id-to-dynamic-c = gen DynId ((X₀ !) ↦ (X₀ ？))

poly-id-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-id-to-dynamic-c ∶ DynId ⊒ PolyId
poly-id-to-dynamic-narrowing =
  checked-narrowing
    (NW.gen (NW.safe-fun (NW.tag (＇ zero)) (NW.untag (＇ zero))))
    is-just

poly-id-reflexive-c : Coercion
poly-id-reflexive-c = `∀ (id X₀ ↦ id X₀)

poly-id-reflexive-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-id-reflexive-c ∶ PolyId ⊒ PolyId
poly-id-reflexive-narrowing =
  checked-narrowing
    (NW.cross
      (NW.`∀
        (NW.cross
          (NW.cross (NW.id-＇ zero) NW.↦
           NW.cross (NW.id-＇ zero)))))
    is-just

poly-k-reflexive-c : Coercion
poly-k-reflexive-c =
  `∀ (`∀ (id X₁ ↦ (id X₀ ↦ id X₁)))

poly-k-reflexive-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-k-reflexive-c ∶ PolyK ⊒ PolyK
poly-k-reflexive-narrowing =
  checked-narrowing
    (NW.cross
      (NW.`∀
        (NW.cross
          (NW.`∀
            (NW.cross
              (NW.cross (NW.id-＇ 1) NW.↦
               NW.cross
                 (NW.cross (NW.id-＇ zero) NW.↦
                  NW.cross (NW.id-＇ 1))))))))
    is-just

poly-k-to-dynamic-c : Coercion
poly-k-to-dynamic-c =
  gen DynK (gen DynK ((X₁ !) ↦ ((X₀ !) ↦ (X₁ ？))))

poly-k-to-dynamic-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-k-to-dynamic-c ∶ DynK ⊒ PolyK
poly-k-to-dynamic-narrowing =
  checked-narrowing
    (NW.gen
      (NW.safe-gen
        (NW.safe-fun (NW.tag (＇ 1))
          (NW.cross (NW.tag (＇ zero) NW.↦ NW.untag (＇ 1))))))
    is-just

poly-k-to-dynamic-first-c : Coercion
poly-k-to-dynamic-first-c =
  gen (`∀ (★ ⇒ X₀ ⇒ ★))
    (`∀ ((X₁ !) ↦ (id X₀ ↦ (X₁ ？))))

poly-k-to-dynamic-first-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-k-to-dynamic-first-c
    ∶ `∀ (★ ⇒ X₀ ⇒ ★) ⊒ PolyK
poly-k-to-dynamic-first-narrowing =
  checked-narrowing
    (NW.gen
      (NW.safe-all
        (NW.cross
          (NW.tag (＇ 1) NW.↦
           NW.cross
             (NW.cross (NW.id-＇ zero) NW.↦ NW.untag (＇ 1))))))
    is-just

poly-k-to-dynamic-second-c : Coercion
poly-k-to-dynamic-second-c =
  `∀ (gen (X₀ ⇒ ★ ⇒ X₀)
    (id X₁ ↦ ((X₀ !) ↦ id X₁)))

poly-k-to-dynamic-second-narrowing :
  id-onlyᵈ ∣ zero ∣ [] ⊢ poly-k-to-dynamic-second-c
    ∶ `∀ (X₀ ⇒ ★ ⇒ X₀) ⊒ PolyK
poly-k-to-dynamic-second-narrowing =
  checked-narrowing
    (NW.cross
      (NW.`∀
        (NW.gen
          (NW.safe-fun (NW.cross (NW.id-＇ 1))
            (NW.cross (NW.tag (＇ zero) NW.↦
                       NW.cross (NW.id-＇ 1)))))))
    is-just
