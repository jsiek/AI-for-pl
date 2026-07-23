module
  proof.NuImprecisionRightSourceAllTargetWidenFrameProof
  where

-- File Charter:
--   * Proves the target-widening frame case of source-universal closing.
--   * Recursively closes the inner body, reconstructs both outer
--     source-universal relations, and invokes the existing target frame.
--   * Contains no recursive knot, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
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
open import QuotientedTermImprecision using (Λ⊑ᵀ; ⊑cast⊑ᵀ)
open import Relation.Binary.PropositionalEquality using (subst)
open import TermTyping using (SealModeStore★)
open import
  proof.NuImprecisionRightSourceAllTargetWidenFrameDef
  using (WorldCoherentRightSourceAllTargetWidenFrameᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetWidenFrame
  )


private
  cast-runtime :
    ∀ {M c} →
    RuntimeOK (M ⟨ c ⟩) →
    RuntimeOK M
  cast-runtime (ok-no (no•-⟨⟩ noM)) = ok-no noM
  cast-runtime (ok-⟨⟩ okM) = okM


world-coherent-right-source-all-target-widen-frame-proofᵀ :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightSourceAllTargetWidenFrameᵀ
world-coherent-right-source-all-target-widen-frame-proofᵀ
    close target-frames {occ = occ}
    prefix coherent exclusive unique wfR
    ok-cast vV noV mode seal★ c⊑ liftρ liftγ inner =
  rightTargetWidenFrame target-frames
    prefix coherent exclusive unique wfR ok-cast
    (Λ vV) (no•-Λ noV) mode
    (subst (SealModeStore★ _) store-eq seal★)
    (subst (λ Σ → _ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _) store-eq c⊑)
    (Λ⊑ᵀ occ liftρ liftγ vV inner)
    (close prefix coherent exclusive unique wfR
      (cast-runtime ok-cast) vV noV liftρ liftγ inner)
  where
  store-eq = rightStoreⁱ-lift-left liftρ
