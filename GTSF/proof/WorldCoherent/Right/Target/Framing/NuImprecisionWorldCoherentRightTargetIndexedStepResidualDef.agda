module
  proof.WorldCoherent.Right.Target.Framing.NuImprecisionWorldCoherentRightTargetIndexedStepResidualDef
  where

-- File Charter:
--   * Defines the result of consuming an observed indexed target step from a
--     completed world-coherent right-value catch-up.
--   * Retains the residual weak result, source-bullet transport, relational
--     store lineage, and all final-world invariants.
--   * Contains no implementation, dispatcher, postulate, hole, permissive
--     option, compatibility alias, or wrapper around dependencies.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])

open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NuReduction using
  ( StoreChange
  ; applyTerm
  ; applyTerms
  ; applyTy
  ; applyTys
  ; _—→[_]_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using
  ( No•
  ; RuntimeOK
  ; Term
  ; Value
  ; ⇑ᵗᵐ
  ; _•
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using
  (_∣_∣_⊢_⦂_)
open import Types using
  ( Ty
  ; TyCtx
  )
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepIndexedResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetResult
  ; targetTailChanges
  ; transportType
  ; weakIndexedResult
  )
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using (WorldCoherentRightValueCatchupIndexedResult)


record WorldCoherentRightTargetIndexedStepResidualResult
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V N′ : Term} {A B : Ty} {χ : StoreChange}
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) : Set₁ where
  constructor world-coherent-right-target-indexed-step-residual
  field
    worldRightResidualIndexedResult :
      WeakOneStepIndexedResult
        {M = V} {N′ = N′} {χ = χ} {ρ = ρ} p

    worldRightResidualSourceChangesEmpty :
      sourceChanges
        (weakIndexedResult worldRightResidualIndexedResult) ≡ []

    worldRightResidualSourceUnchanged :
      sourceResult
        (weakIndexedResult worldRightResidualIndexedResult) ≡ V

    worldRightResidualSourceValue :
      Value V

    worldRightResidualSourceNoBullet :
      No• V

    worldRightResidualTargetValue :
      Value
        (targetResult
          (weakIndexedResult worldRightResidualIndexedResult))

    worldRightResidualTargetNoBullet :
      No•
        (targetResult
          (weakIndexedResult worldRightResidualIndexedResult))

    worldRightResidualStoreLineage :
      WeakOneStepStoreLineage
        (weakIndexedResult worldRightResidualIndexedResult)

    worldRightResidualSourceBulletTransport :
      ∀ {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
        {L M′ : Term} {C C′ : Ty}
        {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ →
      RuntimeOK ((⇑ᵗᵐ L) •) →
      No• M′ →
      Δᴸ ∣ leftStoreⁱ ρ ∣ []
        ⊢ (⇑ᵗᵐ L) • ⦂ C →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ (⇑ᵗᵐ L) • ⊑ M′ ⦂ C ⊑ C′ ∶ q →
      resultCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultLeftCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultRightCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultStore
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ []
        ⊢ᴺ applyTerms
              (sourceChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              ((⇑ᵗᵐ L) •)
          ⊑ applyTerms
              (targetTailChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              (applyTerm χ M′)
        ⦂ applyTys
              (sourceChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              C
          ⊑ applyTys
              (targetTailChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              (applyTy χ C′)
        ∶ transportType
            (weakIndexedResult worldRightResidualIndexedResult) q

    worldRightResidualRuntimeNoBulletTransport :
      ∀ {ρ₀ : StoreImp Φ Δᴸ Δᴿ}
        {M M′ : Term} {C C′ : Ty}
        {q : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ →
      RuntimeOK M →
      No• M′ →
      Δᴸ ∣ leftStoreⁱ ρ ∣ [] ⊢ M ⦂ C →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
        ⊢ᴺ M ⊑ M′ ⦂ C ⊑ C′ ∶ q →
      resultCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultLeftCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultRightCtx
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ resultStore
          (weakIndexedResult worldRightResidualIndexedResult)
        ∣ []
        ⊢ᴺ applyTerms
              (sourceChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              M
          ⊑ applyTerms
              (targetTailChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              (applyTerm χ M′)
        ⦂ applyTys
              (sourceChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              C
          ⊑ applyTys
              (targetTailChanges
                (weakIndexedResult worldRightResidualIndexedResult))
              (applyTy χ C′)
        ∶ transportType
            (weakIndexedResult worldRightResidualIndexedResult) q

    worldRightResidualCoherence :
      WorldCoherent
        (resultStore
          (weakIndexedResult worldRightResidualIndexedResult))

    worldRightResidualSourceNameExclusive :
      SourceNameExclusive
        (resultCtx
          (weakIndexedResult worldRightResidualIndexedResult))

    worldRightResidualAssumptionMembershipUnique :
      AssumptionMembershipUnique
        (resultCtx
          (weakIndexedResult worldRightResidualIndexedResult))

    worldRightResidualTargetStoreWf :
      StoreWf
        (resultRightCtx
          (weakIndexedResult worldRightResidualIndexedResult))
        (rightStoreⁱ
          (resultStore
            (weakIndexedResult worldRightResidualIndexedResult)))

open WorldCoherentRightTargetIndexedStepResidualResult public


WorldCoherentRightTargetIndexedStepResidualᵀ : Set₁
WorldCoherentRightTargetIndexedStepResidualᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {V M′ N′ : Term} {A B : Ty} {χ : StoreChange}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  M′ —→[ χ ] N′ →
  WorldCoherentRightValueCatchupIndexedResult
    {V = V} {M′ = M′} {ρ = ρ} p →
  WorldCoherentRightTargetIndexedStepResidualResult
    {ρ = ρ} {V = V} {N′ = N′} {χ = χ} p
