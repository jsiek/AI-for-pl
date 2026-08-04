module
  proof.WorldCoherent.Source.Terminalization.NuImprecisionWorldCoherentSourceQuotientClosePrefixProof
  where

-- File Charter:
--   * Transports one quotient-closing source pair through a completed inner
--     catch-up and delegates its terminal value to the ranked source worker.
--   * Handles the terminal source-blame branch directly with the two
--     cast-blame reductions, outside the value-indexed rank.
--   * Preserves one independent runtime sibling through the same exact final
--     world as the primary caught result.
--   * Contains no quotient classifier, continuation alias, postulate, hole,
--     permissive option, termination bypass, or obsolete capability wrapper.

open import Agda.Builtin.Equality using (refl)
import CastImprecisionShape as CastShape
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Data.List using ([])
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using
  (ImprecisionShape; _；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  ( applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; blame-⟨⟩
  ; keep
  ; pure-step
  ; ξ-⟨⟩
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
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
  ; _⟨_⟩
  )
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; blame⊑ᵀ
  ; prefix-reflⁱ
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseLemma
  using (left-silent-indexed-prefix-closeᵀ)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixSupport
  using (left-catchup-indexed-prefix-blameᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupInvariant
  ; WeakOneStepResult
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
  ; relatedResults
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; silentIndexedResult
  ; sourceChanges
  ; sourceResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
  )
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (cast-shape-applyCoercions)
open import
  proof.Core.Properties.ReductionProperties
  using (applyTerms-preserves-No•; applyTerms-preserves-RuntimeOK)
open import
  proof.NuCore.Relations.NuImprecisionQuotientedTyping
  using (nu-term-imprecision-target-typing)
open import
  proof.OneStep.NuImprecisionWeakOneStepQuotientCompatibilityTransport
  using (weak-one-step-transport-quotient-widening-compatibleᵀ)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotient-boundary-square)
open import
  proof.Quotient.NuImprecisionQuotientWideningTransport
  using (weak-one-step-transport-quotient-widening-pairᵀ)
open import
  proof.Right.Core.NuImprecisionQuotientDownTransportProof
  using (quotient-down-transportᵀ)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using
  ( lineageEmbedding
  ; lineagePrefix
  ; lineageStore
  ; weak-step-store-lineage
  )
open import
  proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingAlgebra
  using (rel-store-embedding-reflⁱ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  ( world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
  ; world-coherent-left-catchup-prepend-keep-step-runtime-sibling
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Source.Terminalization.NuImprecisionWorldCoherentSourceQuotientCloseAccDef
  using (WorldCoherentSourceQuotientCloseAccᵀ)


private
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


world-coherent-source-quotient-close-prefix-proofᵀ :
  WorldCoherentSourceQuotientCloseAccᵀ →
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ R R′ : Term}
    {C C′ D D′ A A′ E E′ : Ty}
    {d d′ u u′ : Coercion}
    {sD sD′ sU sU′ : ImprecisionShape} {μ μ′ : ModeEnv}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {r : Φ ∣ Δᴸ ⊢ E ⊑ E′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  RuntimeOK ((M ⟨ d ⟩) ⟨ u ⟩) →
  Value M′ →
  No• M′ →
  Inert d′ →
  Inert u′ →
  SpineCastMode (leftStoreⁱ ρ₀) μ →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ d ∶ C ⊒ D →
  CastShape.narrowing CastShape.⊢ᶜ d ⦂ sD →
  SpineCastMode (rightStoreⁱ ρ₀) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing CastShape.⊢ᶜ d′ ⦂ sD′ →
  sD ；⌊ pC ⌋≋ᵖ qD ； sD′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD sD sD′ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  CastShape.widening CastShape.⊢ᶜ u ⦂ sU →
  CastShape.widening CastShape.⊢ᶜ u′ ⦂ sU′ →
  sU ；⌊ pA ⌋≋ᵖ qD ； sU′ →
  ReductionClosedQuotientWideningCompatible
    Φ Δᴸ Δᴿ u u′ qD pA sU sU′ →
  No• R →
  RuntimeOK R′ →
  (inner :
    WorldCoherentLeftCatchupIndexedResult
      {N = M} {V′ = M′} {ρ = ρ⁺} pC) →
  (let result =
         weakIndexedResult
           (catchupIndexedResult (worldCatchupResult inner))
   in
   resultCtx result
     ∣ resultLeftCtx result
     ∣ resultRightCtx result
     ∣ resultStore result ∣ []
     ⊢ᴺ applyTerms (sourceChanges result) R
       ⊑ applyTerms (targetTailChanges result)
           (applyTerm keep R′)
     ⦂ applyTys (sourceChanges result) E
       ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
     ∶ transportType result r) →
  Σ[ caught ∈
    WorldCoherentLeftCatchupIndexedResult
      {N = (M ⟨ d ⟩) ⟨ u ⟩}
      {V′ = (M′ ⟨ d′ ⟩) ⟨ u′ ⟩}
      {ρ = ρ⁺} pA ]
    let result =
          weakIndexedResult
            (catchupIndexedResult (worldCatchupResult caught))
    in
    resultCtx result
      ∣ resultLeftCtx result
      ∣ resultRightCtx result
      ∣ resultStore result ∣ []
      ⊢ᴺ applyTerms (sourceChanges result) R
        ⊑ applyTerms (targetTailChanges result)
            (applyTerm keep R′)
      ⦂ applyTys (sourceChanges result) E
        ⊑ applyTys (targetTailChanges result) (applyTy keep E′)
      ∶ transportType result r
world-coherent-source-quotient-close-prefix-proofᵀ
    terminal {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-unique final-wfL)
    inner-sibling
    with final
world-coherent-source-quotient-close-prefix-proofᵀ
    terminal {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-unique final-wfL)
    inner-sibling
    | inj₁ (vV , noV) =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (terminal vV noV (<-wellFounded _)
      coherent final-exclusive final-unique final-wfL final-ok
      vM′ noM′ inert-d′ inert-u′ final-down final-widening
      (cast-shape-applyCoercions (sourceChanges inner) u-shape)
      u′-shape final-square final-compatible
      inner-noR inner-okR′ inner-sibling)
  where
  inner = weakIndexedResult indexed

  final-down =
    quotient-down-transportᵀ {qD = qD}
      prefix indexed
      mode d⊒ d-shape mode′ d′⊒ d′-shape down-square
      final-unique elimination

  final-widening =
    weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner silent widening-pair

  final-square =
    weak-one-step-transport-quotient-boundary-square
      inner (weakIndexedTypeCoherence indexed) up-square

  final-compatible =
    weak-one-step-transport-quotient-widening-compatibleᵀ
      inner (weakIndexedTypeCoherence indexed)
      final-unique compatible

  final-ok =
    ok-⟨⟩ (ok-⟨⟩ (left-catchup-final-runtime invariant))

  inner-noR =
    applyTerms-preserves-No• (sourceChanges inner) noR

  inner-okR′ =
    applyTerms-preserves-RuntimeOK
      (targetTailChanges inner) okR′

  first-silent =
    left-silent-indexed-prefix-closeᵀ
      prefix widening-pair u-shape u′-shape up-square compatible
      catchup final-unique final-down

  first-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)
world-coherent-source-quotient-close-prefix-proofᵀ
    terminal {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-unique final-wfL)
    inner-sibling
    | inj₂ refl =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (world-coherent-left-catchup-prepend-keep-step-runtime-sibling
      (ξ-⟨⟩ (pure-step blame-⟨⟩))
      (world-coherent-left-catchup-prepend-keep-step-runtime-sibling
        (pure-step blame-⟨⟩)
        (terminal-caught , inner-sibling)))
  where
  inner = weakIndexedResult indexed

  final-down =
    quotient-down-transportᵀ {qD = qD}
      prefix indexed
      mode d⊒ d-shape mode′ d′⊒ d′-shape down-square
      final-unique elimination

  first-silent =
    left-silent-indexed-prefix-closeᵀ
      prefix widening-pair u-shape u′-shape up-square compatible
      catchup final-unique final-down

  first = weakIndexedResult (silentIndexedResult first-silent)

  terminal-relation =
    blame⊑ᵀ
      (nu-term-imprecision-target-typing
        (relatedResults first))

  terminal-caught =
    world-coherent-left-indexed-catchup
      (left-catchup-indexed-prefix-blameᵀ
        prefix-reflⁱ
        (no•-⟨⟩ (no•-⟨⟩ noM′))
        terminal-relation)
      (weak-step-store-lineage
        (resultStore first)
        rel-store-embedding-reflⁱ prefix-reflⁱ)
      coherent final-exclusive final-unique final-wfL

  first-lineage =
    weak-step-store-lineage
      (lineageStore lineage)
      (lineageEmbedding lineage)
      (lineagePrefix lineage)
