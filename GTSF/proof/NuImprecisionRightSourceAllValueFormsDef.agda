module
  proof.NuImprecisionRightSourceAllValueFormsDef
  where

-- File Charter:
--   * Collects the four constructor-form source-value cases of
--     source-universal right-value closing.
--   * Splitting on values before QTI avoids computed context-lift indices in
--     impossible bullet and allocation branches.
--   * This is a flat capability record, not a result, view, outcome, or
--     recursive-plan hierarchy.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility re-export, or broad simulation import.

open import
  proof.NuImprecisionRightSourceAllCastBodyDef
  using (WorldCoherentRightSourceAllCastBodyᵀ)
open import
  proof.NuImprecisionRightSourceAllConstantBodyDef
  using (WorldCoherentRightSourceAllConstantBodyᵀ)
open import
  proof.NuImprecisionRightSourceAllLambdaBodyDef
  using (WorldCoherentRightSourceAllLambdaBodyᵀ)
open import
  proof.NuImprecisionRightSourceAllUniversalBodyDef
  using (WorldCoherentRightSourceAllUniversalBodyᵀ)


record WorldCoherentRightSourceAllValueForms : Set₁ where
  field
    sourceAllLambdaBody :
      WorldCoherentRightSourceAllLambdaBodyᵀ
    sourceAllCastBody :
      WorldCoherentRightSourceAllCastBodyᵀ
    sourceAllUniversalBody :
      WorldCoherentRightSourceAllUniversalBodyᵀ
    sourceAllConstantBody :
      WorldCoherentRightSourceAllConstantBodyᵀ

open WorldCoherentRightSourceAllValueForms public
