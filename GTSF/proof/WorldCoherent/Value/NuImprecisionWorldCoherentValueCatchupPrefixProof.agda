module proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixProof where

-- File Charter:
--   * Implements ambient-prefix world-coherent target-value catch-up.
--   * Takes source-runtime and final quotient semantics as whole
--     higher-order contracts.
--   * Handles terminal, target-frame, prefix, and quotient transport cases
--     structurally without importing the permissive scratch dispatcher.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Coercions using
  (Inert)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
import NarrowWiden as NW
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NarrowWiden using (genSafe→inert)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  ( lift-left-ctx-[]
  )
open import NuStore using (StoreWf)
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; blame
  ; no•-blame
  ; no•-⟨⟩
  ; ok-no
  ; ok-⟨⟩
  ; ƛ_
  ; Λ_
  ; $
  ; _⟨_⟩
  )
open import QuotientedTermImprecision
open import proof.Catchup.Core.NuImprecisionCatchupPrefixSupport
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseLemma
  using (left-silent-indexed-prefix-closeᵀ)
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotient-boundary-square)
open import proof.Right.Core.NuImprecisionQuotientDownTransportProof using
  (quotient-down-transportᵀ)
open import proof.Quotient.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import
  proof.Quotient.NuImprecisionEmbeddedTargetInstantiationCreationProperties
  using
  ( embedded-creation-source-valueᴱ
  ; embedded-creation-target-no-bulletᴱ
  )
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra using
  (rel-store-embedding-reflⁱ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef
open import NuReduction using (keep)
open import proof.Store.Prefix.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupComposition using
  (world-coherent-left-catchup-indexed-resume-silentᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames
open import proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalCatchupDef using
  (WorldCoherentQuotientFinalCatchupᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
open import proof.WorldCoherent.Source.RuntimeSteps.NuImprecisionWorldCoherentSourceRuntimeCatchupDef
open import proof.WorldCoherent.Value.NuImprecisionWorldCoherentValueCatchupPrefixDef using
  (WorldCoherentLeftValueCatchupPrefixᵀ)
open import proof.DGG.Core.NuPreservation using (runtime-ν; runtime-⟨⟩)


left-catchup-final-runtime :
  ∀ {Φ Δᴸ Δᴿ M V′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {result : WeakOneStepResult ρ M V′ A B keep} →
  LeftCatchupInvariant result →
  RuntimeOK (sourceResult result)
left-catchup-final-runtime
    (left-catchup-invariant silent (inj₁ (vV , noV))) =
  ok-no noV
left-catchup-final-runtime
    (left-catchup-invariant silent (inj₂ refl)) =
  ok-no no•-blame


world-coherent-left-catchup-prefix-closeᵀ :
  WorldCoherentQuotientFinalCatchupᵀ →
  ∀ {Φ Δᴸ Δᴿ M M′ C C′ D D′ A A′ d d′ u u′
      sD sD′ sU sU′ μ μ′}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  SpineCastMode (leftStoreⁱ ρ₀) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  narrowing ⊢ᶜ d ⦂ sD →
  SpineCastMode (rightStoreⁱ ρ₀) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  narrowing ⊢ᶜ d′ ⦂ sD′ →
  sD ；⌊ pC ⌋≋ᵖ qD ； sD′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD sD sD′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  widening ⊢ᶜ u ⦂ sU →
  widening ⊢ᶜ u′ ⦂ sU′ →
  sU ；⌊ pA ⌋≋ᵖ qD ； sU′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA sU sU′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = M} {V′ = M′} {ρ = ρ⁺} pC →
  WorldCoherentLeftCatchupIndexedResult
    {N = (M ⟨ d ⟩) ⟨ u ⟩}
    {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
    {ρ = ρ⁺} pA
world-coherent-left-catchup-prefix-closeᵀ
    quotient-final {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-unique final-wfL) =
  world-coherent-left-catchup-indexed-resume-silentᵀ
    (left-silent-indexed-prefix-closeᵀ
      prefix widening-pair u-shape u′-shape up-square compatible
      catchup final-unique final-down)
    (weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage))
    (quotient-final coherent final-exclusive final-wfL final-ok
      vM′ noM′ inert-d′ inert-u′
      final-down final-widening
      (cast-shape-applyCoercions
        (sourceChanges inner) u-shape)
      u′-shape
      (weak-one-step-transport-quotient-boundary-square
        inner (weakIndexedTypeCoherence indexed) up-square)
      final)
  where
  inner = weakIndexedResult indexed

  final-down = quotient-down-transportᵀ {qD = qD}
    prefix indexed
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square
    final-unique elimination

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening-pair

  final-ok = ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant))


world-coherent-left-value-catchup-prefix-proofᵀ :
  WorldCoherentSourceRuntimeCatchupᵀ →
  WorldCoherentQuotientFinalCatchupᵀ →
  WorldCoherentLeftValueCatchupPrefixᵀ
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    rel@(blame⊑ᵀ V′⊢) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-blameᵀ prefix noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vM′ ⟨ inert-d′ ⟩ ⟨ inert-u′ ⟩)
    (no•-⟨⟩ (no•-⟨⟩ noM′))
    (closeᵀ
      (paired-downᵀ {q = qD}
        M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape
        down-square elimination)
      widening-pair pA u-shape u′-shape up-square compatible) =
  world-coherent-left-catchup-prefix-closeᵀ
    quotient-catchup {qD = qD}
    prefix okN vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ (runtime-⟨⟩ okN)) vM′ noM′ M⊑M′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (allocation-prefixᵀ prefix₀ inner N⊢ V′⊢) =
  world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    (store-imp-prefix-transⁱ prefix₀ prefix)
    coherent exclusive unique wfL okN vV′ noV′ inner
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊒ᵀ mode seal★ c⊒ rel q c-shape comp) =
  world-coherent-left-catchup-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒ c-shape comp inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑cast⊑ᵀ mode seal★ c⊑ rel q c-shape comp) =
  world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑ c-shape comp inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↑ᵀ c↑ rel q replace) =
  world-coherent-left-catchup-prefix-target-reveal-castᵀ
    prefix c↑ replace inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (⊑conv↓ᵀ c↓ rel q replace) =
  world-coherent-left-catchup-prefix-target-conceal-castᵀ
    prefix c↓ replace inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′ rel
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN () noV′
    (x⊑xᵀ x∈)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    rel@(ƛ⊑ƛᵀ hA hA′ body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (ƛ _) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN () noV′
    (·⊑·ᵀ L⊑L′ M⊑M′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    rel@(Λ⊑Λᵀ liftρ liftγ vV vW′ body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (Λ vV) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    rel@(Λ⊑ᵀ occ liftρ liftγ vV body) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (Λ vV) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    rel@(target-instantiationᵀ embedded) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN
      (embedded-creation-source-valueᴱ embedded)
      (embedded-creation-target-no-bulletᴱ embedded)
      rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN () noV′
    (α⊑αᵀ vL noL vL′ noL′ pA liftρ liftγ
      L⊑L′ L•⊢ L′•⊢)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (α⊑ᵀ vL noL h⇑A liftρ lift-left-ctx-[]
      L⊑V′ L•⊢ V′⊢) =
  source-bullet source-runtime h⇑A prefix coherent exclusive unique wfL okN
    vV′ noV′ vL noL liftρ lift-left-ctx-[] L⊑V′ L•⊢ V′⊢
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN () noV′
    (ν⊑νᵀ hA hA′ s↑ s′↑ pA pA⇑ liftρ liftγ N⊑N′ replace)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (ν⊑ᵀ hA h⇑A s↑ liftρ lift-left-ctx-[] N⊑V′ replace) =
  source-ν source-runtime prefix hA h⇑A s↑ liftρ lift-left-ctx-[]
    vV′ noV′ inner replace
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-ν okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′ rel@κ⊑κᵀ =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN ($ _) noV′ rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN () noV′
    (⊕⊑⊕ᵀ L⊑L′ M⊑M′)
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vW noW
    rel@(gen⊑groundᵀ mode seal★ (c⊢ , NW.gen safe)
      gH vV vW′ W⊢ V⊑Wtag q) =
  world-coherent-left-indexed-catchup
    (left-catchup-indexed-prefix-valueᵀ
      prefix okN (vV ⟨ genSafe→inert (NW.safe-gen safe) ⟩) noW rel)
    (weak-step-store-lineage _
      rel-store-embedding-reflⁱ prefix-reflⁱ)
    coherent exclusive unique wfL
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (cast⊒⊑ᵀ mode seal★ c⊒ N⊑V′ q c-shape comp) =
  source-narrow source-runtime prefix mode seal★ c⊒
    vV′ noV′ inner q c-shape comp
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (cast⊑⊑ᵀ mode seal★ c⊑ N⊑V′ q c-shape comp) =
  source-widen source-runtime prefix mode seal★ c⊑
    vV′ noV′ inner q c-shape comp
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (paired-revealᵀ
      corresponds c↑ c′↑ replacement N⊑V′) =
  source-paired-reveal source-runtime prefix
    corresponds c↑ c′↑ replacement vV′ noV′ inert inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (paired-concealᵀ
      corresponds c↓ c′↓ replacement N⊑V′) =
  source-paired-conceal source-runtime prefix
    corresponds c↓ c′↓ replacement vV′ noV′ inert inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN
    (vV′ ⟨ inert ⟩) (no•-⟨⟩ noV′)
    (paired-wideningᵀ
      mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
      source-comp target-comp compatible N⊑V′) =
  source-paired-widening source-runtime prefix
    mode seal★ c⊑ c-shape mode′ seal★′ c′⊑ c′-shape
    source-comp target-comp compatible vV′ noV′ inert inner
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (conv↑⊑ᵀ c↑ N⊑V′ q replace) =
  source-reveal source-runtime prefix c↑ vV′ noV′ inner q replace
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup
    prefix coherent exclusive unique wfL okN vV′ noV′
    (conv↓⊑ᵀ c↓ N⊑V′ q replace) =
  source-conceal source-runtime prefix c↓ vV′ noV′ inner q replace
  where
  inner = world-coherent-left-value-catchup-prefix-proofᵀ
    source-runtime quotient-catchup prefix coherent exclusive unique wfL
    (runtime-⟨⟩ okN) vV′ noV′ N⊑V′
