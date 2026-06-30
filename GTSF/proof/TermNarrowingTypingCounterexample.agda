module proof.TermNarrowingTypingCounterexample where

-- File Charter:
--   * Checked documentation that endpoint recovery is false for the legacy raw
--     term-narrowing relation in `TermNarrowing`.
--   * Refutes the tempting theorem that raw term narrowing plus separately
--     typed source/target terms determines the narrowing-index endpoints.
--   * The typed relation added in `TermNarrowing` avoids relying on this false
--     recovery principle.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₁)

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

TermNarrowingTypingIndexStatement : Set₁
TermNarrowingTypingIndexStatement =
  ∀ {Δ σ Σ′ γ Γ Γ′ M M′ p A B} →
  Δ ⊢ σ ꞉ srcStoreⁿ σ ⊒ˢ Σ′ →
  Δ ∣ srcStoreⁿ σ ⊢ γ ꞉ Γ ⊒ᵍ Γ′ →
  Δ ∣ srcStoreⁿ σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ B →
  Δ ∣ σ ∣ γ ⊢ M ⊒ M′ ∶ p →
  Δ ∣ srcStoreⁿ σ ⊢ p ∶ᶜ A ⊒ B

idBoolᶜ :
  ∀ {Δ σ} →
  Δ ∣ srcStoreⁿ σ ⊢ id BoolTy ∶ᶜ BoolTy ⊒ BoolTy
idBoolᶜ = cast-id wfBase refl , cross (id-‵ `𝔹)

zero-⊢ℕ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ∣ [] ⊢ $ (κℕ 0) ⦂ NatTy
zero-⊢ℕ = ⊢$ (κℕ 0)

blame-⊢ℕ :
  ∀ {Δ Σ} →
  Δ ∣ Σ ∣ [] ⊢ blame ⦂ NatTy
blame-⊢ℕ = ⊢blame wfBase

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

Bool≢Nat : BoolTy ≡ NatTy → ⊥
Bool≢Nat ()

no-idBool-as-Nat :
  zero ∣ [] ⊢ id BoolTy ∶ᶜ NatTy ⊒ NatTy →
  ⊥
no-idBool-as-Nat (() , _)

term-narrowing-typing-index-counterexample :
  TermNarrowingTypingIndexStatement →
  ⊥
term-narrowing-typing-index-counterexample theorem =
  no-idBool-as-Nat
    (theorem ⊒ˢ-nil ⊒ᵍ-nil zero-⊢ℕ blame-⊢ℕ raw-counterexample)

TypedTermNarrowingEndpointAlignmentStatement : Set₁
TypedTermNarrowingEndpointAlignmentStatement =
  ∀ {Δ σ M M′ p A B C D} →
  Δ ∣ srcStoreⁿ σ ∣ [] ⊢ M ⦂ C →
  Δ ∣ srcStoreⁿ σ ∣ [] ⊢ M′ ⦂ D →
  Δ ∣ σ ∣ [] ⊢ M ⊒ M′ ∶ p ⦂ A ⊒ B →
  A ≡ C × B ≡ D

typed-counterexample :
  zero ∣ [] ∣ [] ⊢ $ (κℕ 0) ⊒ blame ∶ id BoolTy
    ⦂ BoolTy ⊒ BoolTy
typed-counterexample = ⊒blameᵗ (idBoolᶜ {σ = []})

typed-term-narrowing-endpoint-alignment-counterexample :
  TypedTermNarrowingEndpointAlignmentStatement →
  ⊥
typed-term-narrowing-endpoint-alignment-counterexample theorem =
  Bool≢Nat (proj₁ (theorem zero-⊢ℕ blame-⊢ℕ typed-counterexample))
