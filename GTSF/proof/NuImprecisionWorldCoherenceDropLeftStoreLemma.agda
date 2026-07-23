module
  proof.NuImprecisionWorldCoherenceDropLeftStoreLemma
  where

-- File Charter:
--   * Exposes inverse world-coherence transport through a source-only
--     relational-store lift.
--   * Keeps callers independent of the membership-level proof.
--   * Contains no term relation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import
  proof.NuImprecisionWorldCoherenceDropLeftStoreDef
  using (WorldCoherenceDropLeftStoreᵀ)
open import
  proof.NuImprecisionWorldCoherenceDropLeftStoreProof
  using (world-coherence-drop-left-store-proofᵀ)


world-coherence-drop-left-storeᵀ :
  WorldCoherenceDropLeftStoreᵀ
world-coherence-drop-left-storeᵀ liftρ coherent =
  world-coherence-drop-left-store-proofᵀ liftρ coherent
