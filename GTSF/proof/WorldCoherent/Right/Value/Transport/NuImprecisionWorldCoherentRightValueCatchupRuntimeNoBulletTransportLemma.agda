module
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportLemma
  where

-- File Charter:
--   * Assembles the canonical runtime/no-bullet transport from its two
--     independently checked right-silent transport leaves.
--   * Keeps routine strict-spine checks independent of the large structural
--     proof implementation.
--   * Contains no postulate, hole, permissive option, or compatibility shim.

open import proof.Right.Core.NuImprecisionRightSilentPairedCastTransportProof using
  (right-silent-paired-cast-transport-proofᵀ)
open import
  proof.Right.Core.NuImprecisionRightSilentQuotientWideningPairTransportProof
  using (right-silent-quotient-widening-pair-transport-proofᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportDef
  using (WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ)
open import
  proof.WorldCoherent.Right.Value.Transport.NuImprecisionWorldCoherentRightValueCatchupRuntimeNoBulletTransportProof
  using
  (world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ)


world-coherent-right-value-catchup-runtime-no-bullet-transportᵀ :
  WorldCoherentRightValueCatchupRuntimeNoBulletTransportᵀ
world-coherent-right-value-catchup-runtime-no-bullet-transportᵀ =
  world-coherent-right-value-catchup-runtime-no-bullet-transport-proofᵀ
    right-silent-paired-cast-transport-proofᵀ
    right-silent-quotient-widening-pair-transport-proofᵀ
