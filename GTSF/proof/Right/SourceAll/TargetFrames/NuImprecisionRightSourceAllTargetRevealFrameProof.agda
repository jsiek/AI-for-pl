module
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetRevealFrameProof
  where

-- File Charter:
--   * Proves the target-reveal frame case of source-universal closing.
--   * Recursively closes the inner body, reconstructs both outer
--     source-universal relations, and invokes the existing target frame.
--   * Contains no recursive knot, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Conversion using (RevealConversion)
open import NuTermImprecision using (rightStoreⁱ-lift-left)
open import NuTerms using
  ( no•-Λ
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; RuntimeOK
  ; Λ_
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using (Λ⊑ᵀ; ⊑conv↑ᵀ)
open import Relation.Binary.PropositionalEquality using (subst)
open import
  proof.Right.SourceAll.TargetFrames.NuImprecisionRightSourceAllTargetRevealFrameDef
  using (WorldCoherentRightSourceAllTargetRevealFrameᵀ)
open import
  proof.WorldCoherent.Right.Source.Closing.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.WorldCoherent.Right.Target.Terminalization.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetRevealFrame
  )


private
  cast-runtime :
    ∀ {M c} →
    RuntimeOK (M ⟨ c ⟩) →
    RuntimeOK M
  cast-runtime (ok-no (no•-⟨⟩ noM)) = ok-no noM
  cast-runtime (ok-⟨⟩ okM) = okM


world-coherent-right-source-all-target-reveal-frame-proofᵀ :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightSourceAllTargetRevealFrameᵀ
world-coherent-right-source-all-target-reveal-frame-proofᵀ
    close target-frames {occ = occ}
    prefix coherent exclusive unique wfR
    ok-cast vV noV c↑ liftρ liftγ inner =
  rightTargetRevealFrame target-frames
    prefix coherent exclusive unique wfR ok-cast
    (Λ vV) (no•-Λ noV)
    (subst (λ Σ → RevealConversion _ _ Σ _ _ _ _ _)
      store-eq c↑)
    (Λ⊑ᵀ occ liftρ liftγ vV inner)
    (close prefix coherent exclusive unique wfR
      (cast-runtime ok-cast) vV noV liftρ liftγ inner)
  where
  store-eq = rightStoreⁱ-lift-left liftρ
