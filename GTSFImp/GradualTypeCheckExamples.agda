module GradualTypeCheckExamples where

-- File Charter:
--   * Regression examples for `GradualTypeCheck`.
--   * Exercises polymorphism, dynamic application, primitive operations, and
--     rejection of terms whose synthesized operator/argument types disagree.
--   * Each accepted example is checked at its expected source type.

import Data.Fin as Fin
open import Data.Bool using (true)
open import Data.List using ([])
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import GradualTerms
open import GradualTypeCheck
open import Primitives

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

polyId : GTerm 0
polyId = Λ (ƛ ＇ Fin.zero ⇒ ` 0)

polyId-check :
  IsJust (type-check-expect 0 [] polyId (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero)))
polyId-check = is-just

polyIdNat : GTerm 0
polyIdNat = (polyId `[ ℕᵗ ]) ·[ 0 ] $ (κℕ 42)

polyIdNat-check : IsJust (type-check-expect 0 [] polyIdNat ℕᵗ)
polyIdNat-check = is-just

dynamicIdNat : GTerm 0
dynamicIdNat = (ƛ ★ ⇒ ` 0) ·[ 1 ] $ (κℕ 42)

dynamicIdNat-check : IsJust (type-check-expect 0 [] dynamicIdNat ★)
dynamicIdNat-check = is-just

add-example : GTerm 0
add-example = $ (κℕ 20) ⊕[ addℕ at 2 ] $ (κℕ 22)

add-example-check : IsJust (type-check-expect 0 [] add-example ℕᵗ)
add-example-check = is-just

bad-application : GTerm 0
bad-application = $ (κℕ 0) ·[ 3 ] $ (κℕ 1)

bad-application-rejected : type-check 0 [] bad-application ≡ nothing
bad-application-rejected = refl

bad-addition : GTerm 0
bad-addition = $ (κ𝔹 true) ⊕[ addℕ at 4 ] $ (κℕ 1)

bad-addition-rejected : type-check 0 [] bad-addition ≡ nothing
bad-addition-rejected = refl
