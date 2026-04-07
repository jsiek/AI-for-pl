module extrinsic.TypeSafety where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List using ([])

open import extrinsic.Reduction
open import extrinsic.Progress using (Progress; progress)
open import extrinsic.Preservation using (preservation; multi-preservation)

------------------------------------------------------------------------
-- Closed-term type safety wrapper
------------------------------------------------------------------------

record Safety {Δ : TyCtx} (M : Term) (A : Ty) : Set where
  constructor safety
  field
    progress-witness : Progress M
    preservation-step : ∀ {N : Term} → M —→ N → Δ ∣ [] ⊢ N ⦂ A

open Safety public

typeSafety :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ∣ [] ⊢ M ⦂ A →
  Safety {Δ} M A
typeSafety hM = safety (progress hM) (preservation hM)

typeSafety-↠ :
  ∀ {Δ : TyCtx} {M N : Term} {A : Ty} →
  Δ ∣ [] ⊢ M ⦂ A →
  M —↠ N →
  Δ ∣ [] ⊢ N ⦂ A
typeSafety-↠ = multi-preservation

typeSafety-steps :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ∣ [] ⊢ M ⦂ A →
  (Σ (Progress M) (λ _ → ∀ {N : Term} → M —→ N → Δ ∣ [] ⊢ N ⦂ A))
typeSafety-steps hM = progress hM , preservation hM
