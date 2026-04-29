module curry.proof.TypeSafety where

open import Data.Product using (Σ; ∃; ∃-syntax; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using ([])

open import curry.Reduction
open import curry.Progress using (Progress; progress; done; step)
open import curry.Preservation using (preservation; multi-preservation)

------------------------------------------------------------------------
-- Closed-term type safety wrapper
------------------------------------------------------------------------

record Safety {Δ : TyCtx} (M : Term) (A : Ty) : Set where
  constructor safety
  field
    progress-witness : Progress M
    preservation-step : ∀ {N : Term} → M —→ N → Δ ⊢ [] ⊢ N ⦂ A

open Safety public

typeSafety :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  Safety {Δ} M A
typeSafety hM = safety (progress hM) (preservation hM)

typeSafety-↠ :
  ∀ {Δ : TyCtx} {M N : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  M —↠ N →
  Δ ⊢ [] ⊢ N ⦂ A
typeSafety-↠ = multi-preservation

type-safety :
  ∀ {Δ : TyCtx} {M N : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  M —↠ N →
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety hM M—↠N with progress (multi-preservation hM M—↠N)
... | step s = inj₁ (_ , s)
... | done v = inj₂ v
