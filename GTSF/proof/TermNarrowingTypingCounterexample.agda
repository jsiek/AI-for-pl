module proof.TermNarrowingTypingCounterexample where

-- File Charter:
--   * Checked counterexample to the hoped-for exact typing/index theorem for
--     arbitrary term narrowing.
--   * Shows that source/target typing plus a typed context narrowing is not
--     enough to recover the term-narrowing index at the source/target types.
--   * The obstruction is the intentionally permissive `⊒blame` constructor.

open import Agda.Builtin.Equality using (refl)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_,_)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import TermNarrowing

TermNarrowingTypingIndexStatement : Set₁
TermNarrowingTypingIndexStatement =
  ∀ {Δ σ Σ′ γ Γ Γ′ M M′ p A B} →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ γ ꞉ Γ ⊒ᵍ Γ′ →
  Δ ∣ srcStoreⁿ σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B

ℕ0 : Term
ℕ0 = $ (κℕ 0)

id𝔹ᶜ : zero ∣ [] ⊢ id (‵ `𝔹) ∶ᶜ ‵ `𝔹 ⊒ ‵ `𝔹
id𝔹ᶜ = cast-id wfBase refl , cross (id-‵ `𝔹)

ℕ0⊢ : zero ∣ [] ∣ [] ⊢ ℕ0 ⦂ ‵ `ℕ
ℕ0⊢ = ⊢$ (κℕ 0)

blameℕ⊢ : zero ∣ [] ∣ [] ⊢ blame ⦂ ‵ `ℕ
blameℕ⊢ = ⊢blame wfBase

bad-narrowing :
  zero ∣ [] ∣ [] ⊢ ℕ0 ⊒ blame ∶ id (‵ `𝔹)
bad-narrowing = ⊒blame id𝔹ᶜ

no-id𝔹-as-ℕ :
  zero ∣ [] ⊢ id (‵ `𝔹) ∶ᶜ ‵ `ℕ ⊒ ‵ `ℕ →
  ⊥
no-id𝔹-as-ℕ (() , _)

term-narrowing-typing-index-counterexample :
  TermNarrowingTypingIndexStatement →
  ⊥
term-narrowing-typing-index-counterexample theorem =
  no-id𝔹-as-ℕ
    (theorem ⊒ˢ-nil ⊒ᵍ-nil ℕ0⊢ blameℕ⊢ bad-narrowing)
