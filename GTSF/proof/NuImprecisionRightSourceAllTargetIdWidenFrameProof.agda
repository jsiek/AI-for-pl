module
  proof.NuImprecisionRightSourceAllTargetIdWidenFrameProof
  where

-- File Charter:
--   * Proves the identity-mode target-widening frame case of
--     source-universal closing.
--   * Recursively closes the inner body, reconstructs both outer
--     source-universal relations, and invokes the existing target frame.
--   * Contains no recursive knot, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Coercions using (id-onlyᵈ)
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
open import QuotientedTermImprecision using (Λ⊑ᵀ; ⊑cast⊑idᵀ)
open import Relation.Binary.PropositionalEquality using (subst)
open import TermTyping using (SealModeStore★)
open import
  proof.NuImprecisionRightSourceAllTargetIdWidenFrameDef
  using (WorldCoherentRightSourceAllTargetIdWidenFrameᵀ)
open import
  proof.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)
open import
  proof.NuImprecisionWorldCoherentRightTargetCastTerminalizationDef
  using
  ( WorldCoherentRightTargetCastTerminalization
  ; rightTargetIdWidenFrame
  )


private
  cast-runtime :
    ∀ {M c} →
    RuntimeOK (M ⟨ c ⟩) →
    RuntimeOK M
  cast-runtime (ok-no (no•-⟨⟩ noM)) = ok-no noM
  cast-runtime (ok-⟨⟩ okM) = okM


world-coherent-right-source-all-target-id-widen-frame-proofᵀ :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightTargetCastTerminalization →
  WorldCoherentRightSourceAllTargetIdWidenFrameᵀ
world-coherent-right-source-all-target-id-widen-frame-proofᵀ
    close target-frames {occ = occ}
    prefix coherent exclusive unique wfR
    ok-cast vV noV seal★ c⊑ liftρ liftγ inner =
  rightTargetIdWidenFrame target-frames
    prefix coherent exclusive unique wfR ok-cast
    (Λ vV) (no•-Λ noV)
    (subst (SealModeStore★ id-onlyᵈ) store-eq seal★)
    (subst (λ Σ → id-onlyᵈ ∣ _ ∣ Σ ⊢ _ ∶ _ ⊑ _)
      store-eq c⊑)
    (Λ⊑ᵀ occ liftρ liftγ vV inner)
    (close prefix coherent exclusive unique wfR
      (cast-runtime ok-cast) vV noV liftρ liftγ inner)
  where
  store-eq = rightStoreⁱ-lift-left liftρ
