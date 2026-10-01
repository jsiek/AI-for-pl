module Validation where

-- File Charter:
--   * Forces Agda to normalize Consistency2.lower? on the Python model's
--     validation examples.
--   * Records the direct polymorphic-identity evidence and the free-name
--     cross-mode case that lower? intentionally misses.

open import Data.Fin using (zero; suc)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Consistency
open import Consistency2

ℕᵗ 𝔹ᵗ : Ty 0
ℕᵗ = ‵ `ℕ
𝔹ᵗ = ‵ `𝔹

dynFun : Ty 0
dynFun = ★ ⇒ ★

∀X⇒X ∀X⇒★ ∀X allDyn : Ty 0
∀X⇒X = `∀ (＇ zero ⇒ ＇ zero)
∀X⇒★ = `∀ (＇ zero ⇒ ★)
∀X = `∀ (＇ zero)
allDyn = `∀ ★

∀∀outer : Ty 0
∀∀outer = `∀ (`∀ (＇ (suc zero)))

lower-01 : lower? ℕᵗ ℕᵗ ≡ just ℕᵗ
lower-01 = refl

lower-02 : lower? ℕᵗ 𝔹ᵗ ≡ nothing
lower-02 = refl

lower-03 : lower? ℕᵗ ★ ≡ just ℕᵗ
lower-03 = refl

lower-04 : lower? ★ 𝔹ᵗ ≡ just 𝔹ᵗ
lower-04 = refl

lower-05 : lower? (ℕᵗ ⇒ 𝔹ᵗ) dynFun ≡ just (ℕᵗ ⇒ 𝔹ᵗ)
lower-05 = refl

lower-06 : lower? ∀X⇒X ∀X⇒X ≡ just ∀X⇒X
lower-06 = refl

lower-07 : lower? ∀X⇒X dynFun ≡ just ∀X⇒X
lower-07 = refl

lower-08 : lower? ∀X allDyn ≡ just ∀X
lower-08 = refl

lower-09 : lower? allDyn ∀X ≡ just ∀X
lower-09 = refl

lower-10 : lower? ∀X ★ ≡ just ∀X
lower-10 = refl

lower-11 : lower? ∀X⇒★ ∀X⇒X ≡ nothing
lower-11 = refl

lower-12 : lower? ∀∀outer ∀∀outer ≡ just ∀∀outer
lower-12 = refl

identity-direct : ∀X⇒X ∼ ∀X⇒X
identity-direct = ∀ᶜ (id (＇ zero) ↦ id (＇ zero))

all-all-inst-gen : allDyn ∼ ∀∀outer
all-all-inst-gen =
  gen_ ⦃ nonvar-all ⦄ ⦃ ∈-all var-∈ ⦄
    (∀ᶜ (？ (id (＇ (suc zero))))) (λ ())

cross-X-star : idᶜ {Δ = 1} ⊢ ＇ zero ∼ ★
cross-X-star = (id (＇ zero)) !

lower-cross-X-star : lower? {Δ = 1} (＇ zero) ★ ≡ nothing
lower-cross-X-star = refl
