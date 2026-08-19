module proof.DGG.Inversion.TargetWalkLemma where

-- File Charter:
--   * Exposes the target tag/seal walk factory conditional on the pinned
--     occupied non-star source-seal residual.
--   * Stitches the source-strip and atom-core factories into the target-walk
--     statement.
--   * Does not expose source-strip internals.

open import Data.Product using (_,_)

open import proof.DGG.Inversion.SourceStripLemma using
  (source-spine-strip; source-tag-seal-core)
open import proof.DGG.Inversion.SourceStripDef using
  (core-tagged; spine-paired; spine-sealed; spine-tagged)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)
open import proof.DGG.Inversion.TargetWalkSupport using
  (OccupiedNonStarSourceSealResidual)

target-tag-seal-walk : OccupiedNonStarSourceSealResidual
  → TargetTagSealWalk
target-tag-seal-walk occupied
    {U = U} {S = S} {Y = Y} {ν = ν} {cY = cY}
    sv vU mono rb sc X∈ Y∈ D
    with source-spine-strip occupied {U = U} {S = S} {Y = Y}
      {ν = ν} {cY = cY} sv vU mono rb sc X∈ Y∈ D
target-tag-seal-walk occupied
    {U = U} {S = S} {Y = Y} {ν = ν} {cY = cY}
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-sealed Pᵖ Aᵖ spineᵖ sealed finish =
  finish sealed
target-tag-seal-walk occupied
    {U = U} {S = S} {Y = Y} {ν = ν} {cY = cY}
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-tagged Pᵖ Aᵖ spineᵖ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
          boundaryᵖᵒ source∈ᵒ target∈ᵒ premiseᶜ finish =
  finish
    (source-tag-seal-core
      {Wᵒ = Wᵒ} {Wᵖ = Wᵖ}
      {γᵒ = γᵒ} {γᵖ = γᵖ}
      {P = Pᵖ} {U = U} {A = Aᵖ} {S = S}
      {Xᴸ = Xᵒ} {Y = Y} {ν = ν} {cY = cY}
      {p = pᵖ} {q = qᵒ}
      spineᵖ vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      (core-tagged premiseᶜ))
target-tag-seal-walk occupied
    {U = U} {S = S} {Y = Y} {ν = ν} {cY = cY}
    sv vU mono rb sc X∈ Y∈ D
    | P , A , Xᵒ , Wᵒ , γᵒ , qᵒ , spine ,
        spine-paired Pᵖ Aᵖ spineᵖ paired finish =
  finish paired
