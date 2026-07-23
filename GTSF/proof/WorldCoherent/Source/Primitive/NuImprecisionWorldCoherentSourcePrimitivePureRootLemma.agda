module
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootLemma
  where

-- File Charter:
--   * Assembles the complete primitive pure-root capability from canonical
--     delta scheduling and source-blame leaves.
--   * Keeps the unfinished right-value catch-up engine as one explicit
--     higher-order dependency.
--   * Contains no postulate, hole, permissive option, or broad DGG import.

open import proof.Source.OneStep.NuImprecisionSourceOneStepBlameRootLemma using
  (world-coherent-source-keep-blame-rootᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupLemma
  using (world-coherent-source-primitive-delta-catchupᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootCasesDef
  using (WorldCoherentSourcePrimitivePureRootCases)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootDef
  using (WorldCoherentSourcePrimitivePureRootᵀ)
open import
  proof.WorldCoherent.Source.Primitive.NuImprecisionWorldCoherentSourcePrimitivePureRootProof
  using (world-coherent-source-primitive-pure-root-proofᵀ)


world-coherent-source-primitive-pure-rootᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentSourcePrimitivePureRootᵀ
world-coherent-source-primitive-pure-rootᵀ right-catchup =
  world-coherent-source-primitive-pure-root-proofᵀ cases
  where
  cases : WorldCoherentSourcePrimitivePureRootCases
  cases = record
    { sourcePrimitiveDeltaCatchupCase =
        world-coherent-source-primitive-delta-catchupᵀ right-catchup
    ; sourcePrimitiveBlameRootCase =
        world-coherent-source-keep-blame-rootᵀ
    }
