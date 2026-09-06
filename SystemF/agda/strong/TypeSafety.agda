module strong.TypeSafety where

-- TYPE SAFETY for Strong System F (v2, the conversion-boundary calculus).
--
-- The public theorem surface, stated in full and proven by thin wrappers
-- over strong.Progress, strong.Preservation and strong.Reduction:
--
--   progress      a well-typed closed term is a value or steps
--   preservation  a step preserves the type (and preservation* along a run)
--   type-safety   after any run, a well-typed closed term is a value or
--                 steps again — it never gets stuck
--   det           reduction is deterministic
--   value-¬step   values do not step
--
-- All five hold with NO parameters and NO postulates (--safe).  The
-- reduction relation is indexed by the type context Δ only; the term
-- context is empty, as it must be (see strong.Preservation).

open import Data.List using ([])
open import Data.Sum using (_⊎_)
open import Data.Product using (Σ; Σ-syntax)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_)
import strong.Reduction as R
import strong.Progress as Pr
import strong.Preservation as Pv
import strong.proof.TypeSafety as TS

------------------------------------------------------------------------
-- Progress
------------------------------------------------------------------------

progress : ∀ {Δ : Ctxᵗ} {M : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
    ---------------------------------------------
  → Value M ⊎ (Σ[ M′ ∈ Term ] (Δ ⊢ M -→ M′))
progress = Pr.progress

------------------------------------------------------------------------
-- Preservation
------------------------------------------------------------------------

preservation : ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→ M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A
preservation = Pv.preservation

preservation* : ∀ {Δ : Ctxᵗ} {M M′ : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* M′
    ----------------
  → Δ ∣ [] ⊢ M′ ⦂ A
preservation* = Pv.preservation*

------------------------------------------------------------------------
-- Type safety
------------------------------------------------------------------------

type-safety : ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* N
    ---------------------------------------------
  → Value N ⊎ (Σ[ N′ ∈ Term ] (Δ ⊢ N -→ N′))
type-safety = TS.type-safety

------------------------------------------------------------------------
-- Determinism, and values do not step
------------------------------------------------------------------------

det : ∀ {Δ : Ctxᵗ} {M M₁ M₂ : Term}
  → Δ ⊢ M -→ M₁
  → Δ ⊢ M -→ M₂
    -------------
  → M₁ ≡ M₂
det = R.det

value-¬step : ∀ {Δ : Ctxᵗ} {M M′ : Term}
  → Value M
  → Δ ⊢ M -→ M′
    -------------
  → ⊥
value-¬step = R.value-¬step
