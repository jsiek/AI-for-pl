module
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootLemma
  where

-- File Charter:
--   * Assembles the complete primitive pure-root capability from canonical
--     delta scheduling and source-blame leaves.
--   * Keeps the unfinished right-value catch-up engine as one explicit
--     higher-order dependency.
--   * Contains no postulate, hole, permissive option, or broad DGG import.

open import proof.NuImprecisionSourceOneStepBlameRootLemma using
  (world-coherent-source-keep-blame-rootᵀ)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupLemma
  using (world-coherent-source-primitive-delta-catchupᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootCasesDef
  using (WorldCoherentSourcePrimitivePureRootCases)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootDef
  using (WorldCoherentSourcePrimitivePureRootᵀ)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootProof
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
