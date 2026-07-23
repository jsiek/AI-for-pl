module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsProof
  where

-- File Charter:
--   * Assembles the four source-value-form capabilities.
--   * Supplies the completed constant impossibility proof canonically while
--     retaining the three semantic shape proofs as explicit parameters.
--   * Contains no recursion, result/view/outcome type, postulate, hole,
--     permissive option, or broad simulation import.

open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyDef
  using (WorldCoherentRightSourceAllCastBodyᵀ)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllCastBodyProof
  using (world-coherent-right-source-all-cast-body-proofᵀ)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllConstantBodyProof
  using (world-coherent-right-source-all-constant-body-proofᵀ)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyDef
  using (WorldCoherentRightSourceAllLambdaBodyᵀ)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllLambdaBodyProof
  using (world-coherent-right-source-all-lambda-body-proofᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyDef
  using (WorldCoherentRightSourceAllUniversalBodyᵀ)
open import
  proof.Right.SourceAll.Core.NuImprecisionRightSourceAllUniversalBodyProof
  using (world-coherent-right-source-all-universal-body-proofᵀ)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsDef
  using (WorldCoherentRightSourceAllValueForms)
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingCasesDef
  using (WorldCoherentRightSourceAllClosingCases)


world-coherent-right-source-all-value-forms-proof :
  WorldCoherentRightSourceAllClosingCases →
  WorldCoherentRightSourceAllValueForms
world-coherent-right-source-all-value-forms-proof
    cases = record
  { sourceAllLambdaBody =
      world-coherent-right-source-all-lambda-body-proofᵀ cases
  ; sourceAllCastBody =
      world-coherent-right-source-all-cast-body-proofᵀ cases
  ; sourceAllUniversalBody =
      world-coherent-right-source-all-universal-body-proofᵀ cases
  ; sourceAllConstantBody =
      world-coherent-right-source-all-constant-body-proofᵀ
  }
