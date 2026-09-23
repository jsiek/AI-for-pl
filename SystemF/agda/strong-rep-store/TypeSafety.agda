module strong-rep-store.TypeSafety where

-- File Charter:
--   * THE WHOLE PUBLIC THEOREM SURFACE, STATED EXPLICITLY IN ONE
--     PLACE: `Progress`, `Preservation`, `PreservationWf`,
--     `Preservation*` and `TypeSafety`, the last being the
--     COMPOSITION of progress and preservation at `runCtx r`.  `det`
--     and `value-¬step` are re-stated here too.
--   * NO PROOFS AND NO DEFINITIONS: every right-hand side delegates.
--   * A STEP RETURNS THE CHANGE IT MADE TO THE STORE, so preservation
--     MOVES the context and `det` concludes the PAIR `(M′ , δ)` is
--     unique.
--   * THE PREMISES ARE NOT UNIFORM, AND THAT IS THE POINT.
--     `preservation` takes `WfCtx Δ` (the premise-free form is FALSE);
--     `progress` takes none; `det` takes the REDEX'S TYPING
--     DERIVATION.
-- Commentary: Commentary.md § TypeSafety.agda

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ; WfCtx; Alloc; apply)
open import strong-rep-store.Terms using (Term; Ctx; Value; _∣_⊢_⦂_)
open import strong-rep-store.Reduction
  using (_⊢_-→_∣_; _⊢_-→*_; runCtx)
import strong-rep-store.Reduction as R
import strong-rep-store.proof.Determinism as D
import strong-rep-store.Progress as Pr
import strong-rep-store.Preservation as Pv
import strong-rep-store.proof.TypeSafety as TS

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

Progress : Set
Progress = ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] Σ[ δ ∈ Alloc ] (Δ ⊢ M -→ M′ ∣ δ))

Preservation : Set
Preservation = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    -----------------------
  → apply δ Δ ∣ [] ⊢ M′ ⦂ A

PreservationWf : Set
PreservationWf = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty} {δ : Alloc}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′ ∣ δ
    -----------------
  → WfCtx (apply δ Δ)

Preservation* : Set
Preservation* = ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* M′)
    ------------------------
  → runCtx r ∣ [] ⊢ M′ ⦂ A

TypeSafety : Set
TypeSafety = ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → WfCtx Δ
  → Δ ∣ [] ⊢ M ⦂ A
  → (r : Δ ⊢ M -→* N)
    ---------------------------------------------
  → Value N ⊎ (Σ[ N′ ∈ Term ] Σ[ δ ∈ Alloc ] (runCtx r ⊢ N -→ N′ ∣ δ))

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

preservation : Preservation
preservation = Pv.preservation

preservation-wf : PreservationWf
preservation-wf = Pv.preservation-wf

preservation* : Preservation*
preservation* = Pv.preservation*

progress : Progress
progress = Pr.progress

type-safety : TypeSafety
type-safety = TS.type-safety

------------------------------------------------------------------------
-- Determinism, and values do not step — unconditional
------------------------------------------------------------------------

-- The contractum AND the store change are functions of the redex.
det : ∀ {Δ : Ctxᵗ} {Γ : Ctx} {M M₁ M₂ : Term} {A : Ty} {δ₁ δ₂ : Alloc}
  → Δ ∣ Γ ⊢ M ⦂ A
  → Δ ⊢ M -→ M₁ ∣ δ₁
  → Δ ⊢ M -→ M₂ ∣ δ₂
    -------------------------
  → (M₁ ≡ M₂) × (δ₁ ≡ δ₂)
det = D.det

value-¬step : ∀ {Δ : Ctxᵗ} {M M′ : Term} {δ : Alloc}
  → Value M
  → Δ ⊢ M -→ M′ ∣ δ
    -------------
  → ⊥
value-¬step = R.value-¬step
