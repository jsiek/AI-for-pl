module TypeSafety where

-- File Charter:
--   * States GTNF's type-safety interface: progress with blame,
--     one-step and multi-step preservation, determinism, and
--     irreducibility of values and blame.
--   * Contains statements only.  Implementations live under
--     proof/TypeSafety/ and will later be exposed by thin wrappers.
--   * A reduction step returns its allocation, so preservation types the
--     result at `apply δ Δ`, and determinism identifies both the result and
--     the allocation.

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax; _×_; ∃-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty)
open import Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import Coercion using (Label)
open import Terms using (Term; Ctx; Value; blame; _∣_⊢_⦂_)
open import Reduction using (_⊢_-→_∣_; _⊢_-→*_; runCtx)

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Value M
    ⊎ (∃[ ℓ ] M ≡ blame ℓ)
    ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))

Preservation : Set
Preservation = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
  → apply δ Δ ∣ [] ⊢ M′ ⦂ A

PreservationWf : Set
PreservationWf = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
  → WfCtx (apply δ Δ)

Preservation* : Set
Preservation* = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* M′)
  → runCtx r ∣ [] ⊢ M′ ⦂ A

Determinism : Set
Determinism = ∀ {Δ : Ctxᵗ} {Γ : Ctx} {M M₁ M₂ : Term}
    {A : Ty} {δ₁ δ₂ : Alloc}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
  → (M₁ ≡ M₂) × (δ₁ ≡ δ₂)

Irreducible : Set
Irreducible =
  (∀ {Δ : Ctxᵗ} {M M′ : Term} {δ : Alloc}
    → Value M
    → Δ ⊢ M -→ M′ ∣ δ
    → ⊥)
  ×
  (∀ {Δ : Ctxᵗ} {M′ : Term} {δ : Alloc} {ℓ : Label}
    → Δ ⊢ blame ℓ -→ M′ ∣ δ
    → ⊥)
