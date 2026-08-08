module SliceCheck where

-- Scratch-only validation for the recut target-strip slice surface.
-- Checks that the public seal/tag slices still assemble to the strip
-- members and remain compatible with the source-strip walk composition.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore; source-strip)
open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)

------------------------------------------------------------------------
-- Validation A: sliced corollaries at the public recut indices
------------------------------------------------------------------------

target-strip★-from-slices-check :
  SealDescentAtVar
  → TagDispatchAt★
  → TargetStripAt★
target-strip★-from-slices-check =
  target-strip★-from-slices

target-strip★ᴸ-from-slices-check :
  SealDescentAtVarᴸ
  → TagDispatchAt★ᴸ
  → TargetStripAt★ᴸ
target-strip★ᴸ-from-slices-check =
  target-strip★ᴸ-from-slices

------------------------------------------------------------------------
-- Validation B: source strip workers remain expressible
------------------------------------------------------------------------

record SharedFoldConsumers : Set₁ where
  field
    source-column : SourceColumnStrip
    source-spine : SourceSpineStrip
    seal-descent : SealDescentAtVar
    seal-descentᴸ : SealDescentAtVarᴸ
    tag-dispatch : TagDispatchAt★
    tag-dispatchᴸ : TagDispatchAt★ᴸ
    source-core : SourceTagSealCore

shared-target-strip :
  SharedFoldConsumers
  → TargetStripAt★
shared-target-strip consumers =
  target-strip★-from-slices seal-descent tag-dispatch
  where
  open SharedFoldConsumers consumers

shared-target-stripᴸ :
  SharedFoldConsumers
  → TargetStripAt★ᴸ
shared-target-stripᴸ consumers =
  target-strip★ᴸ-from-slices seal-descentᴸ tag-dispatchᴸ
  where
  open SharedFoldConsumers consumers

walk-from-shared-fold-consumers :
  SharedFoldConsumers
  → TargetTagSealWalk
walk-from-shared-fold-consumers consumers {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    with source-spine sv vU mono rb sc X∈ Y∈ D
  where
  open SharedFoldConsumers consumers
walk-from-shared-fold-consumers consumers {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Wᵒ γᵒ qᵒ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
        boundaryᵖᵒ atom source∈ᵒ target∈ᵒ premiseᶜ resume =
  resume
    (source-core {Xᴸ = Xᴸ} {q = qᵒ}
      atom vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      premiseᶜ)
  where
  open SharedFoldConsumers consumers
