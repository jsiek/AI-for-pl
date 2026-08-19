module proof.DGG.Inversion.SourceStripLemma where

-- File Charter:
--   * Exposes source-strip factories at the Def types, conditional on the
--     pinned occupied non-star source-seal residual.
--   * Stitches the parameterized source-strip proof to the quarantined legacy
--     worker module.
--   * Re-exports no target-walk or right-injection theorem.

import proof.DGG.Inversion.SourceStripProof as Proof
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore)
open import proof.DGG.Inversion.SourceStripWorkerProof using
  (source-column-strip-worker; source-spine-strip-worker)
open import proof.DGG.Inversion.TargetWalkSupport using
  (OccupiedNonStarSourceSealResidual)

module ClosedSourceStrip (occupied : OccupiedNonStarSourceSealResidual) =
  Proof.SourceStripProofFrom
    (source-column-strip-worker occupied)
    (source-spine-strip-worker occupied)

source-column-strip : OccupiedNonStarSourceSealResidual
  → SourceColumnStrip
source-column-strip occupied =
  ClosedSourceStrip.source-column-strip occupied

source-spine-strip : OccupiedNonStarSourceSealResidual
  → SourceSpineStrip
source-spine-strip occupied =
  ClosedSourceStrip.source-spine-strip occupied

source-tag-seal-core : SourceTagSealCore
source-tag-seal-core
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ}
    {Wᵒ = Wᵒ} {Wᵖ = Wᵖ}
    {γᵒ = γᵒ} {γᵖ = γᵖ}
    {P = P} {U = U} {A = A} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {ν = ν} {cY = cY}
    {p = p} {q = q}
    sv vU mono rb sc source∈ target∈ premise =
  Proof.source-tag-seal-core
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ}
    {Wᵒ = Wᵒ} {Wᵖ = Wᵖ}
    {γᵒ = γᵒ} {γᵖ = γᵖ}
    {P = P} {U = U} {A = A} {S = S}
    {Xᴸ = Xᴸ} {Y = Y} {ν = ν} {cY = cY}
    {p = p} {q = q}
    sv vU mono rb sc source∈ target∈ premise
