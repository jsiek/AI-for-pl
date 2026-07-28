module
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupProof
  where

-- File Charter:
--   * Implements the accumulated-world live quotient `closeᵀ`
--     runtime-sibling adapter from one exact-final terminal contract.
--   * Transports arbitrary narrowing modes, quotient widening evidence, and
--     both compatibility conditions through the completed inner catch-up.
--   * Uses the shared exact silent-resumption sibling join, so the caught
--     result and sibling are composed from the same final world.
--   * Contains no quotient classifier duplication, allocation recovery,
--     retired special case, postulate, hole, or permissive option.

open import Agda.Builtin.Equality using (refl)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; narrowing; widening)
open import Coercions using
  (Coercion; Inert; ModeEnv)
open import Data.List using ([])
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
  ; keep
  )
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; no•-blame
  ; ok-no
  ; ok-⟨⟩
  ; _⟨_⟩
  )
open import QuotientedTermImprecision using
  ( QuotientWideningPair
  ; StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import QuotientImprecisionCompatibility using
  ( QuotientNarrowingEliminationCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; SpineCastMode
  )
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Core.NuImprecisionCatchupPrefixCloseLemma
  using (left-silent-indexed-prefix-closeᵀ)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( LeftCatchupInvariant
  ; WeakOneStepResult
  ; catchupIndexedResult
  ; left-catchup-invariant
  ; left-indexed-catchup
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  ; weakIndexedTypeCoherence
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (cast-shape-applyCoercions)
open import proof.Core.Properties.ReductionProperties using
  (applyTerms-preserves-No•; applyTerms-preserves-RuntimeOK)
open import
  proof.OneStep.NuImprecisionWeakOneStepReplacementTransport
  using (weak-one-step-transport-quotient-boundary-square)
open import proof.Quotient.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
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
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupRuntimeSiblingComposition
  using
  (world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using
  ( WorldCoherentLeftCatchupIndexedResult
  ; worldCatchupResult
  ; world-coherent-left-indexed-catchup
  )
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ)
open import
  proof.WorldCoherent.Quotient.Final.NuImprecisionWorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupDef
  using (WorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupᵀ)


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


world-coherent-quotient-final-close-runtime-sibling-catchupᵀ :
  WorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupᵀ →
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
world-coherent-quotient-final-close-runtime-sibling-catchupᵀ
    terminal {qD = qD} prefix okM
    vM′ noM′ inert-d′ inert-u′
    mode d⊒ d-shape mode′ d′⊒ d′-shape down-square elimination
    widening-pair u-shape u′-shape up-square compatible noR okR′
    (world-coherent-left-indexed-catchup
      catchup@(left-indexed-catchup indexed
        invariant@(left-catchup-invariant
          silent@(left-silent-invariant refl refl) final))
      lineage coherent final-exclusive final-unique final-wfL)
    inner-sibling =
  world-coherent-left-catchup-indexed-resume-silent-runtime-siblingᵀ
    first-silent first-lineage
    (terminal coherent final-exclusive final-unique final-wfL
      final-ok vM′ noM′ inert-d′ inert-u′
      final-down final-widening
      (cast-shape-applyCoercions
        (sourceChanges inner) u-shape)
      u′-shape
      (weak-one-step-transport-quotient-boundary-square
        inner (weakIndexedTypeCoherence indexed) up-square)
      final inner-noR inner-okR′ inner-sibling)
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


world-coherent-quotient-final-runtime-sibling-catchup-proofᵀ :
  WorldCoherentQuotientFinalTerminalRuntimeSiblingCatchupᵀ →
  WorldCoherentQuotientFinalRuntimeSiblingCatchupᵀ
world-coherent-quotient-final-runtime-sibling-catchup-proofᵀ terminal =
  record
    { quotient-close-sibling =
        world-coherent-quotient-final-close-runtime-sibling-catchupᵀ
          terminal
    }
