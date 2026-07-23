module proof.NuImprecisionWorldCoherentSourceKeepRelationLemma where

-- File Charter:
--   * Exposes the canonical exact source-`keep` result constructor.
--   * Contains no semantic recursion, postulate, hole, or permissive option.

open import proof.NuImprecisionWorldCoherentSourceKeepRelationDef using
  (WorldCoherentSourceKeepRelationᵀ)
open import proof.NuImprecisionWorldCoherentSourceKeepRelationProof using
  (world-coherent-source-keep-relation-proofᵀ)


world-coherent-source-keep-relationᵀ :
  WorldCoherentSourceKeepRelationᵀ
world-coherent-source-keep-relationᵀ =
  world-coherent-source-keep-relation-proofᵀ
