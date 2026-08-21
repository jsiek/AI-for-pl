module proof.DGG.Inversion.SourceStripLemma where

-- File Charter:
--   * Exposes source-strip factories at the Def types.
--   * Stitches the parameterized source-strip proof to the quarantined legacy
--     worker module.
--   * Re-exports no target-walk or right-injection theorem.

import proof.DGG.Inversion.SourceStripProof as Proof
open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore)
open import proof.DGG.Inversion.SourceStripWorkerProof using
  (source-column-strip-worker; source-spine-strip-worker)
module ClosedSourceStrip =
  Proof.SourceStripProofFrom
    source-column-strip-worker source-spine-strip-worker

source-column-strip : SourceColumnStrip
source-column-strip = ClosedSourceStrip.source-column-strip

source-spine-strip : SourceSpineStrip
source-spine-strip = ClosedSourceStrip.source-spine-strip

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
