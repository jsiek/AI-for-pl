module
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionDef
  where

-- File Charter:
--   * Defines the exact coercion-body inversion shared by the two pending
--     target-`ν` allocation cells whose final precision index is paired.
--   * Exposes the forced universal source-body shape and separates the inert
--     all-coercion residual from the active nested-instantiation residual.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, catch-all, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert; ModeEnv; inst)
open import Data.Product using (_×_; ∃-syntax)
open import Data.Sum using (_⊎_)
open import NarrowWiden using (InstSafe; _∣_∣_⊢_∶_⊑_)
open import Types using (Ty; TyCtx; `∀)


WorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionᵀ :
  Set
WorldCoherentRightTargetPendingNuAllocationPairedFinalBodyInversionᵀ =
  ∀ {μ : ModeEnv} {Δ : TyCtx} {Σ}
    {C E : Ty} {s : Coercion} →
  μ ∣ Δ ∣ Σ ⊢ inst (`∀ E) s ∶ `∀ C ⊑ `∀ E →
  ∃[ C₀ ]
    (C ≡ `∀ C₀) ×
    (Inert s ⊎
     ∃[ B ] ∃[ t ]
       (s ≡ inst B t) × InstSafe t)
