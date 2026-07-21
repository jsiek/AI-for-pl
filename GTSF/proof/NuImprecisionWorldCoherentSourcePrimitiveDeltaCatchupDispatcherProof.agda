module
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDispatcherProof
  where

-- File Charter:
--   * Assembles general source-delta catch-up by structural relation
--     recursion.
--   * Delegates the unframed primitive to direct scheduling and transports
--     completed results through all five target cast/conversion forms.
--   * Contains no direct scheduling, catch-all, postulate, hole, or option.

open import QuotientedTermImprecision using
  ( allocation-prefixᵀ
  ; ⊑cast⊒ᵀ
  ; ⊑cast⊑ᵀ
  ; ⊑cast⊑idᵀ
  ; ⊑conv↑ᵀ
  ; ⊑conv↓ᵀ
  ; ⊑αᵀ
  ; ⊑νᵀ
  ; ⊑νcastᵀ
  ; ⊕⊑⊕ᵀ
  )
open import
  proof.NuImprecisionWorldCoherentSourceOneStepTargetCastFramesDef
  using
  ( sourceStepTargetConcealFrame
  ; sourceStepTargetIdWidenFrame
  ; sourceStepTargetNarrowFrame
  ; sourceStepTargetRevealFrame
  ; sourceStepTargetWidenFrame
  )
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupCasesDef
  using
  ( WorldCoherentSourcePrimitiveDeltaCatchupCases
  ; sourcePrimitiveDeltaDirectCase
  ; sourcePrimitiveDeltaTargetCastFrames
  )
open import
  proof.NuImprecisionWorldCoherentSourcePrimitiveDeltaCatchupDef
  using (WorldCoherentSourcePrimitiveDeltaCatchupᵀ)
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.NuPreservation using (runtime-⟨⟩)


world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ :
  WorldCoherentSourcePrimitiveDeltaCatchupCases →
  WorldCoherentSourcePrimitiveDeltaCatchupᵀ
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (allocation-prefixᵀ prefix₀ inner M⊢ M′⊢) =
  world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive wfR okM′ inner
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑αᵀ {q = ()} vL′ noL′ hA liftρ liftγ inner r N⊢ L′•⊢)
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑νᵀ {q = ()} hA h⇑A s↑ liftρ liftγ r inner)
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑νcastᵀ {q = ()} mode seal★ s⊑ liftρ liftγ r inner)
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊕⊑⊕ᵀ L⊑L′ R⊑R′) =
  sourcePrimitiveDeltaDirectCase cases
    prefix coherent exclusive wfR okM′ L⊑L′ R⊑R′
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑cast⊒ᵀ mode seal★ c⊒ inner q) =
  sourceStepTargetNarrowFrame target-frames
    prefix mode seal★ c⊒ recursive
  where
  target-frames = sourcePrimitiveDeltaTargetCastFrames cases
  recursive =
    world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
      cases prefix coherent exclusive wfR (runtime-⟨⟩ okM′) inner
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑cast⊑ᵀ mode seal★ c⊑ inner q) =
  sourceStepTargetWidenFrame target-frames
    prefix mode seal★ c⊑ recursive
  where
  target-frames = sourcePrimitiveDeltaTargetCastFrames cases
  recursive =
    world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
      cases prefix coherent exclusive wfR (runtime-⟨⟩ okM′) inner
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑cast⊑idᵀ seal★ c⊑ inner q) =
  sourceStepTargetIdWidenFrame target-frames
    prefix seal★ c⊑ recursive
  where
  target-frames = sourcePrimitiveDeltaTargetCastFrames cases
  recursive =
    world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
      cases prefix coherent exclusive wfR (runtime-⟨⟩ okM′) inner
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑conv↑ᵀ c↑ inner q) =
  sourceStepTargetRevealFrame target-frames prefix c↑ recursive
  where
  target-frames = sourcePrimitiveDeltaTargetCastFrames cases
  recursive =
    world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
      cases prefix coherent exclusive wfR (runtime-⟨⟩ okM′) inner
world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
    cases prefix coherent exclusive wfR okM′
    (⊑conv↓ᵀ c↓ inner q) =
  sourceStepTargetConcealFrame target-frames prefix c↓ recursive
  where
  target-frames = sourcePrimitiveDeltaTargetCastFrames cases
  recursive =
    world-coherent-source-primitive-delta-catchup-dispatcher-proofᵀ
      cases prefix coherent exclusive wfR (runtime-⟨⟩ okM′) inner
