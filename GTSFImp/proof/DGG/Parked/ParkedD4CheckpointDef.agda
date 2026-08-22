module proof.DGG.Parked.ParkedD4CheckpointDef where

-- File Charter:
--   * States the D4 higher-order-shared-arg parked checkpoint.
--   * Names the concrete store-change trace through the two parked
--     allocations found by Phase3DeepDives.
--   * Contains only theorem carriers and no permissive option.

import Data.List as List

open import Reduction using (StoreChanges; []; _∷_; keep; bind)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.Examples2 as Ex2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.ReachabilityCatalog as RC
open import proof.DGG.Parked.ParkedWorldDef using
  (ParkedEvolve; ParkedWorld)

open CTI2 using (_∣_⊢²_⊑_∶_)


D4-χ₀₈ : StoreChanges 0 2
D4-χ₀₈ =
  bind RC.∀X⇒X₀ ∷
  keep ∷
  keep ∷
  keep ∷
  keep ∷
  keep ∷
  keep ∷
  bind (RC.ℕᵗ {Δ = 1}) ∷
  []


D4-parked-world₀ᵀ : Set
D4-parked-world₀ᵀ =
  ParkedWorld P3.higher-order-shared-arg-world₀


D4-parked-evolve₀₈ᵀ : Set
D4-parked-evolve₀₈ᵀ =
  ParkedEvolve D4-χ₀₈ D4-χ₀₈
    P3.higher-order-shared-arg-world₀
    P3.higher-order-shared-arg-world₂


D4-parked-world₂ᵀ : Set
D4-parked-world₂ᵀ =
  ParkedWorld P3.higher-order-shared-arg-world₂


D4-checkpointᵀ : Set
D4-checkpointᵀ =
  P3.higher-order-shared-arg-world₂ ∣ List.[] ⊢²
    P3.higher-order-shared-arg₈
    ⊑ P3.higher-order-shared-arg₈
    ∶ Ex2.ℕ⊑ℕ² {W = P3.higher-order-shared-arg-world₂}
