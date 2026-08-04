module
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllClosingDispatcherProof
  where

-- File Charter:
--   * Exhaustively dispatches source-universal right-value closing over the
--     four constructor forms of the source value.
--   * Splits on constructor-form indices before shape-specific QTI inversion,
--     avoiding computed left/right context-lift unification in this layer.
--   * Delegates all semantics to flat value-form capabilities.
--   * Contains no recursion, result/view/outcome type, postulate, hole,
--     incomplete match, permissive option, or broad simulation import.

open import NuTerms using
  ( no•-$
  ; no•-ƛ
  ; no•-Λ
  ; no•-⟨⟩
  ; ƛ_
  ; Λ_
  ; $
  ; _⟨_⟩
  )
open import
  proof.Right.SourceAll.ClosingValues.NuImprecisionRightSourceAllValueFormsDef
  using
  ( WorldCoherentRightSourceAllValueForms
  ; sourceAllCastBody
  ; sourceAllConstantBody
  ; sourceAllLambdaBody
  ; sourceAllUniversalBody
  )
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)


world-coherent-right-source-all-closing-dispatcher-proofᵀ :
  WorldCoherentRightSourceAllValueForms →
  WorldCoherentRightSourceAllClosingᵀ
world-coherent-right-source-all-closing-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okN′
    (ƛ N) (no•-ƛ noN) liftρ liftγ rel =
  sourceAllLambdaBody cases prefix coherent exclusive unique
    wfR okN′ noN liftρ liftγ rel
world-coherent-right-source-all-closing-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okN′
    (vM ⟨ inert ⟩) (no•-⟨⟩ noM) liftρ liftγ rel =
  sourceAllCastBody cases prefix coherent exclusive unique
    wfR okN′ vM noM inert liftρ liftγ rel
world-coherent-right-source-all-closing-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okN′
    (Λ vU) (no•-Λ noU) liftρ liftγ rel =
  sourceAllUniversalBody cases prefix coherent exclusive unique
    wfR okN′ vU noU liftρ liftγ rel
world-coherent-right-source-all-closing-dispatcher-proofᵀ
    cases prefix coherent exclusive unique wfR okN′
    ($ k) no•-$ liftρ liftγ rel =
  sourceAllConstantBody cases prefix coherent exclusive unique
    wfR okN′ liftρ liftγ rel
