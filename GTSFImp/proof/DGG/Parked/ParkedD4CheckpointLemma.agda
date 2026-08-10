module proof.DGG.Parked.ParkedD4CheckpointLemma where

-- File Charter:
--   * Exposes the D4 higher-order-shared-arg parked evolution and full
--     post-allocation v2 relation checkpoint.
--   * Keeps callers independent of the checkpoint worker proof.
--   * Contains only total checked definitions and no wrapper carrier.

open import proof.DGG.Parked.ParkedD4CheckpointDef using
  ( D4-checkpointᵀ
  ; D4-parked-evolve₀₈ᵀ
  ; D4-parked-world₀ᵀ
  ; D4-parked-world₂ᵀ
  )
open import proof.DGG.Parked.ParkedD4CheckpointProof using
  ( D4-checkpoint-proofᵀ
  ; D4-parked-evolve₀₈-proofᵀ
  ; D4-parked-world₀-proofᵀ
  ; D4-parked-world₂-proofᵀ
  )


D4-parked-world₀ : D4-parked-world₀ᵀ
D4-parked-world₀ = D4-parked-world₀-proofᵀ


D4-parked-evolve₀₈ : D4-parked-evolve₀₈ᵀ
D4-parked-evolve₀₈ = D4-parked-evolve₀₈-proofᵀ


D4-parked-world₂ : D4-parked-world₂ᵀ
D4-parked-world₂ = D4-parked-world₂-proofᵀ


D4-checkpoint : D4-checkpointᵀ
D4-checkpoint = D4-checkpoint-proofᵀ
