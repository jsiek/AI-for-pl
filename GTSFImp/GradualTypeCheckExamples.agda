module GradualTypeCheckExamples where

-- File Charter:
--   * Regression examples for `GradualTypeCheck`.
--   * Exercises polymorphism, dynamic application, primitive operations, and
--     rejection of terms whose synthesized operator/argument types disagree.
--   * Each accepted example has a checker-produced typing derivation; closed
--     data examples are compiled and evaluated to their expected result.

import Data.Fin as Fin
open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import GradualTerms
open import GradualTypeCheck
open import Primitives
open import TyStore using (store-empty)
open import Compile using (compile)
import Example as Ex

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

polyId : GTerm 0
polyId = Λ (ƛ ＇ Fin.zero ⇒ ` 0)

polyId-check :
  IsJust (type-check-expect 0 [] polyId (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero)))
polyId-check = is-just

polyId-⊢ : 0 ∣ [] ⊢ polyId ⦂ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
polyId-⊢ =
  fromJust
    (type-check-expect 0 [] polyId (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero)))
    polyId-check

polyIdNat : GTerm 0
polyIdNat = (polyId `[ ℕᵗ ]) ·[ 0 ] $ (κℕ 42)

polyIdNat-check : IsJust (type-check-expect 0 [] polyIdNat ℕᵗ)
polyIdNat-check = is-just

polyIdNat-⊢ : 0 ∣ [] ⊢ polyIdNat ⦂ ℕᵗ
polyIdNat-⊢ =
  fromJust (type-check-expect 0 [] polyIdNat ℕᵗ) polyIdNat-check

polyIdNat-eval :
  Ex.evalNat Ex.gas
    (proj₂ (compile {Σ = store-empty} polyIdNat-⊢)) ≡ just 42
polyIdNat-eval = refl

dynamicIdNat : GTerm 0
dynamicIdNat =
  (ƛ ℕᵗ ⇒ ` 0) ·[ 2 ] ((ƛ ★ ⇒ ` 0) ·[ 1 ] $ (κℕ 42))

dynamicIdNat-check : IsJust (type-check-expect 0 [] dynamicIdNat ℕᵗ)
dynamicIdNat-check = is-just

dynamicIdNat-⊢ : 0 ∣ [] ⊢ dynamicIdNat ⦂ ℕᵗ
dynamicIdNat-⊢ =
  fromJust
    (type-check-expect 0 [] dynamicIdNat ℕᵗ)
    dynamicIdNat-check

dynamicIdNat-eval :
  Ex.evalNat Ex.gas
    (proj₂ (compile {Σ = store-empty} dynamicIdNat-⊢)) ≡ just 42
dynamicIdNat-eval = refl

add-example : GTerm 0
add-example = $ (κℕ 20) ⊕[ addℕ at 2 ] $ (κℕ 22)

add-example-check : IsJust (type-check-expect 0 [] add-example ℕᵗ)
add-example-check = is-just

add-example-⊢ : 0 ∣ [] ⊢ add-example ⦂ ℕᵗ
add-example-⊢ =
  fromJust (type-check-expect 0 [] add-example ℕᵗ) add-example-check

add-example-eval :
  Ex.evalNat Ex.gas
    (proj₂ (compile {Σ = store-empty} add-example-⊢)) ≡ just 42
add-example-eval = refl

bad-application : GTerm 0
bad-application = $ (κℕ 0) ·[ 3 ] $ (κℕ 1)

bad-application-rejected : type-check 0 [] bad-application ≡ nothing
bad-application-rejected = refl

bad-addition : GTerm 0
bad-addition = $ (κ𝔹 true) ⊕[ addℕ at 4 ] $ (κℕ 1)

bad-addition-rejected : type-check 0 [] bad-addition ≡ nothing
bad-addition-rejected = refl
