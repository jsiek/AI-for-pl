module proof.DGG.Inversion.TargetWalkProof where

-- File Charter:
--   * Derives the target tag/seal walk from the source-strip and atom-core
--     rebuild surfaces.
--   * Contains only the composition proof; source-column mechanics live in
--     `SourceStripProof`.
--   * Exposes no right-injection theorem directly.

open import proof.DGG.Inversion.SourceStripDef using
  (SourceSpineStrip; SourceTagSealCore; SourceSpineStripResult;
   core-paired; core-tagged; source-strip; terminal-paired;
   terminal-rebuild; terminal-tagged)
open import proof.DGG.Inversion.SourceStripLemma using
  (source-spine-strip; source-tag-seal-core)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)

target-walk-from-strip :
  SourceSpineStrip
  → SourceTagSealCore
  → TargetTagSealWalk
target-walk-from-strip strip core sv vU mono rb sc X∈ Y∈ D
    with strip sv vU mono rb sc X∈ Y∈ D
target-walk-from-strip strip core sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-rebuild rebuild)
        resume =
  resume rebuild
target-walk-from-strip strip core sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-tagged Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ
          source∈ᵒ target∈ᵒ premiseᶜ)
        resume =
  resume
    (core {Xᴸ = Xᵒ} {q = qᵒ}
      spine vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      (core-tagged premiseᶜ))
target-walk-from-strip strip core sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-paired Wᵖ γᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ
          source∈ᵒ target∈ᵒ repᵒ rᵖ premiseᵖ)
        resume =
  resume
    (core-paired Wᵖ γᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ source∈ᵒ
      target∈ᵒ repᵒ rᵖ premiseᵖ)

target-tag-seal-walk : TargetTagSealWalk
target-tag-seal-walk sv vU mono rb sc X∈ Y∈ D
    with source-spine-strip sv vU mono rb sc X∈ Y∈ D
target-tag-seal-walk sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-rebuild rebuild)
        resume =
  resume rebuild
target-tag-seal-walk sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-tagged Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ
          source∈ᵒ target∈ᵒ premiseᶜ)
        resume =
  resume
    (source-tag-seal-core {Xᴸ = Xᵒ} {q = qᵒ}
      spine vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ source∈ᵒ target∈ᵒ
      (core-tagged premiseᶜ))
target-tag-seal-walk sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Xᵒ Wᵒ γᵒ qᵒ spine
        (terminal-paired Wᵖ γᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ
          source∈ᵒ target∈ᵒ repᵒ rᵖ premiseᵖ)
        resume =
  resume
    (core-paired Wᵖ γᵖ monoᵒᵖ sameᵒᵖ boundaryᵖᵒ source∈ᵒ
      target∈ᵒ repᵒ rᵖ premiseᵖ)
