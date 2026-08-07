module proof.DGG.Parked.ParkedWorldLemma where

-- File Charter:
--   * Exposes the parked-world closure, transport, geometry, and stage-1
--     right-extension bridge lemmas.
--   * Keeps downstream DGG tracks independent of the worker proof scripts.
--   * Contains only total checked definitions and no wrapper carrier.

open import proof.DGG.Parked.ParkedWorldDef using
  ( MapCtxᴾᵀ
  ; ParkedFreshBothᴸᵀ
  ; ParkedFreshBothᴿᵀ
  ; ParkedFreshLeftᴸᵀ
  ; ParkedFreshRightᴿᵀ
  ; ParkedFreshZeroᵀ
  ; ParkedNoCrossingᵀ
  ; ParkedTargetIdentityᵀ
  ; ParkedTargetStableᵀ
  ; ParkedWorldClosedᵀ
  ; RightOnlyParked→WorldExtendᴿᵀ
  ; Transport⊑ᴾᵀ
  ; WorldExtendᴿ→RightOnlyParkedᵀ
  )
open import proof.DGG.Parked.ParkedWorldProof using
  ( mapCtxᴾ-proofᵀ
  ; parked-fresh-bothᴸ-proofᵀ
  ; parked-fresh-bothᴿ-proofᵀ
  ; parked-fresh-leftᴸ-proofᵀ
  ; parked-fresh-rightᴿ-proofᵀ
  ; parked-fresh-zero-proofᵀ
  ; parked-no-crossing-proofᵀ
  ; parked-target-identity-proofᵀ
  ; parked-target-stable-proofᵀ
  ; parked-world-closed-proofᵀ
  ; right-only-parked→world-extendᴿ-proofᵀ
  ; transport⊑ᴾ-proofᵀ
  ; world-extendᴿ→right-only-parked-proofᵀ
  )


parked-world-closed : ParkedWorldClosedᵀ
parked-world-closed = parked-world-closed-proofᵀ


transport⊑ᴾ : Transport⊑ᴾᵀ
transport⊑ᴾ = transport⊑ᴾ-proofᵀ


mapCtxᴾ : MapCtxᴾᵀ
mapCtxᴾ = mapCtxᴾ-proofᵀ


parked-target-stable : ParkedTargetStableᵀ
parked-target-stable = parked-target-stable-proofᵀ


parked-target-identity : ParkedTargetIdentityᵀ
parked-target-identity = parked-target-identity-proofᵀ


parked-fresh-bothᴸ : ParkedFreshBothᴸᵀ
parked-fresh-bothᴸ = parked-fresh-bothᴸ-proofᵀ


parked-fresh-bothᴿ : ParkedFreshBothᴿᵀ
parked-fresh-bothᴿ = parked-fresh-bothᴿ-proofᵀ


parked-fresh-leftᴸ : ParkedFreshLeftᴸᵀ
parked-fresh-leftᴸ = parked-fresh-leftᴸ-proofᵀ


parked-fresh-rightᴿ : ParkedFreshRightᴿᵀ
parked-fresh-rightᴿ = parked-fresh-rightᴿ-proofᵀ


parked-fresh-zero : ParkedFreshZeroᵀ
parked-fresh-zero = parked-fresh-zero-proofᵀ


parked-no-crossing : ParkedNoCrossingᵀ
parked-no-crossing = parked-no-crossing-proofᵀ


right-only-parked→world-extendᴿ :
  RightOnlyParked→WorldExtendᴿᵀ
right-only-parked→world-extendᴿ =
  right-only-parked→world-extendᴿ-proofᵀ


world-extendᴿ→right-only-parked :
  WorldExtendᴿ→RightOnlyParkedᵀ
world-extendᴿ→right-only-parked =
  world-extendᴿ→right-only-parked-proofᵀ
