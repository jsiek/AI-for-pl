module
  proof.OneStep.NuImprecisionLambdaInstBetaFinalTargetAtomicImpossibleDef
  where

-- File Charter:
--   * States that the renamed final target type stored by `Λ⊑instβᵀ`
--     cannot be atomic.
--   * Retains exactly the typed `inst` widening and target-type renaming
--     equation available at the atomic target reindexing boundary.
--   * Contains no term relation, implementation, result/view/outcome type,
--     postulate, hole, permissive option, termination bypass, catch-all
--     clause, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import Coercions as C
open C using
  (Coercion; ModeEnv)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import Types using
  (Atom; Renameᵗ; Store; Ty; TyCtx; renameᵗ; ⇑ᵗ; `∀)


LambdaInstBetaFinalTargetAtomicImpossibleᵀ : Set
LambdaInstBetaFinalTargetAtomicImpossibleᵀ =
  ∀ {μ : ModeEnv} {Δ : TyCtx} {Σ : Store}
    {B C A′ : Ty} {s : Coercion} {σ : Renameᵗ} →
  μ ∣ Δ ∣ Σ ⊢ C.inst B s ∶ `∀ C ⊑ B →
  renameᵗ σ (⇑ᵗ B) ≡ A′ →
  Atom A′ →
  ⊥
