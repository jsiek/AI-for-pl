module strong.proof.TypeSafety where

-- TYPE SAFETY for Strong System F: the composition of progress and
-- preservation along a run.  The two theorems are proven elsewhere
-- (strong.Progress, strong.Preservation); this module only puts them
-- together.  The public statement lives in strong.TypeSafety.

open import Data.List using ([])
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import strong.Types using (Ty)
open import strong.Ctx using (Ctxᵗ)
open import strong.Terms using (Term; Value; _∣_⊢_⦂_)
open import strong.Reduction using (_⊢_-→_; _⊢_-→*_)
open import strong.Progress using (progress)
open import strong.Preservation using (preservation*)

-- A well-typed closed term, after any number of steps, is a value or
-- can step again — it never gets stuck.
type-safety : ∀ {Δ : Ctxᵗ} {M N : Term} {A : Ty}
  → Δ ∣ [] ⊢ M ⦂ A
  → Δ ⊢ M -→* N
  → Value N ⊎ (Σ[ N′ ∈ Term ] (Δ ⊢ N -→ N′))
type-safety ⊢M M-→*N = progress (preservation* ⊢M M-→*N)
