module
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootProof
  where

-- File Charter:
--   * Assembles the complete primitive pure-root capability.
--   * Dispatches delta to general target catch-up and both blame roots to the
--     shared source-blame capability.
--   * Contains no semantic leaf proof, catch-all, postulate, hole, or option.

open import NuReduction using
  (blame-⊕₁; blame-⊕₂; pure-step; δ-⊕)
open import TermTyping using (⊢⊕)
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootCasesDef
  using
  ( WorldCoherentSourcePrimitivePureRootCases
  ; sourcePrimitiveBlameRootCase
  ; sourcePrimitiveDeltaCatchupCase
  )
open import
  proof.NuImprecisionWorldCoherentSourcePrimitivePureRootDef
  using (WorldCoherentSourcePrimitivePureRootᵀ)


world-coherent-source-primitive-pure-root-proofᵀ :
  WorldCoherentSourcePrimitivePureRootCases →
  WorldCoherentSourcePrimitivePureRootᵀ
world-coherent-source-primitive-pure-root-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    (⊢⊕ L⊢ op R⊢) M′⊢ M⊑M′ δ-⊕ =
  sourcePrimitiveDeltaCatchupCase cases
    prefix coherent exclusive wfR okM′ M⊑M′
world-coherent-source-primitive-pure-root-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ blame-⊕₁ =
  sourcePrimitiveBlameRootCase cases
    prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step blame-⊕₁)
world-coherent-source-primitive-pure-root-proofᵀ
    cases prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (blame-⊕₂ vL) =
  sourcePrimitiveBlameRootCase cases
    prefix coherent exclusive wfL wfR okM okM′
    M⊢ M′⊢ M⊑M′ (pure-step (blame-⊕₂ vL))
