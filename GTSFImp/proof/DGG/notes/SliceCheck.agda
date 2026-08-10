module SliceCheck where

-- Scratch-only validation for the recut target-strip slice surface.
-- Checks that the public seal/tag slices still assemble to the strip
-- members and remain compatible with the source-strip walk composition.

open import Data.Product using (_,_)

open import proof.DGG.Inversion.SourceStripDef using
  (SourceColumnStrip; SourceSpineStrip; SourceTagSealCore; core-tagged;
   spine-paired; spine-sealed; spine-tagged)
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
walk-from-shared-fold-consumers consumers
    sv vU mono rb sc X∈ Y∈ D
    with source-spine sv vU mono rb sc X∈ Y∈ D
  where
  open SharedFoldConsumers consumers
walk-from-shared-fold-consumers consumers
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-sealed Pᵖ Aᵖ spineᵖ sealed finish =
  finish sealed
walk-from-shared-fold-consumers consumers
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-tagged Pᵖ Aᵖ spineᵖ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
          boundaryᵖᵒ source∈ᵒ target∈ᵒ premiseᶜ finish =
  finish
    (source-core {Xᴸ = Xᵒ} {q = qᵒ}
      spineᵖ vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      (core-tagged premiseᶜ))
  where
  open SharedFoldConsumers consumers
walk-from-shared-fold-consumers consumers
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-paired Pᵖ Aᵖ spineᵖ paired finish =
  finish paired
  where
  open SharedFoldConsumers consumers
