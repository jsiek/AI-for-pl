module proof.TermNarrowingTypingCounterexample where

-- File Charter:
--   * Checked documentation that endpoint recovery is false for the raw
--     term-narrowing relation in `TermNarrowing`.
--   * Exhibits `$ 0 ⊒ blame ∶ id 𝔹` even though `$ 0` has type `ℕ`.
--   * This module is intentionally about the legacy raw relation; the typed
--     relation added in `TermNarrowing` avoids relying on such recovery.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (_,_)

open import Types
open import Coercions
open import Primitives
open import NuTerms
open import NarrowWiden
open import TermNarrowing

BoolTy : Ty
BoolTy = ‵ `𝔹

NatTy : Ty
NatTy = ‵ `ℕ

idBoolᶜ :
  ∀ {Δ σ} →
  Δ ∣ srcStoreⁿ σ ⊢ id BoolTy ∶ᶜ BoolTy ⊒ BoolTy
idBoolᶜ = cast-id wfBase refl , cross (id-‵ `𝔹)

zero-⊢ℕ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ∣ [] ⊢ $ (κℕ 0) ⦂ NatTy
zero-⊢ℕ = ⊢$ (κℕ 0)

blame-⊢𝔹 :
  ∀ {Δ Σ} →
  Δ ∣ Σ ∣ [] ⊢ blame ⦂ BoolTy
blame-⊢𝔹 = ⊢blame wfBase

raw-counterexample :
  ∀ {Δ σ} →
  Δ ∣ σ ∣ [] ⊢ $ (κℕ 0) ⊒ blame ∶ id BoolTy
raw-counterexample {σ = σ} = ⊒blame (idBoolᶜ {σ = σ})

Nat≢Bool : NatTy ≡ BoolTy → ⊥
Nat≢Bool ()
