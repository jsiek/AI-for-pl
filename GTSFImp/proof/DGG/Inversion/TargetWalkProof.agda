module proof.DGG.Inversion.TargetWalkProof where

-- File Charter:
--   * Derives the target tag/seal walk from the source-strip and atom-core
--     rebuild surfaces.
--   * Contains only the composition proof; source-column mechanics live in
--     `SourceStripProof`.
--   * Exposes no right-injection theorem directly.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceSpineStrip; SourceTagSealCore; SourceSpineStripResult;
   source-strip)
open import proof.DGG.Inversion.SourceStripLemma using
  (source-spine-strip; source-tag-seal-core)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)

target-walk-from-strip :
  SourceSpineStrip
  → SourceTagSealCore
  → TargetTagSealWalk
target-walk-from-strip strip core {Xᴸ = Xᴸ} sv vU mono rb sc X∈ Y∈ D
    with strip sv vU mono rb sc X∈ Y∈ D
target-walk-from-strip strip core {Xᴸ = Xᴸ} sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Wᵒ γᵒ qᵒ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
        boundaryᵖᵒ atom source∈ᵒ target∈ᵒ premiseᶜ resume =
  resume
    (core {Xᴸ = Xᴸ} {q = qᵒ}
      atom vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      premiseᶜ)

target-tag-seal-walk : TargetTagSealWalk
target-tag-seal-walk {Xᴸ = Xᴸ} sv vU mono rb sc X∈ Y∈ D
    with source-spine-strip sv vU mono rb sc X∈ Y∈ D
target-tag-seal-walk {Xᴸ = Xᴸ} sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Wᵒ γᵒ qᵒ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
        boundaryᵖᵒ atom source∈ᵒ target∈ᵒ premiseᶜ resume =
  resume
    (source-tag-seal-core {Xᴸ = Xᴸ} {q = qᵒ}
      atom vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      premiseᶜ)
