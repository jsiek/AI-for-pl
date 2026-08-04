module
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootCasesDef
  where

-- File Charter:
--   * Defines the two semantic capabilities needed by primitive pure roots.
--   * Separates general delta catch-up from the shared source-blame root.
--   * Contains no dispatcher, implementation, postulate, hole, or option.

open import proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootDef using
  (WorldCoherentSourceKeepBlameRootᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupᵀ)


record WorldCoherentSourcePrimitivePureRootCases : Set₁ where
  field
    sourcePrimitiveDeltaCatchupCase :
      WorldCoherentSourcePrimitiveDeltaCatchupᵀ

    sourcePrimitiveBlameRootCase :
      WorldCoherentSourceKeepBlameRootᵀ

open WorldCoherentSourcePrimitivePureRootCases public
