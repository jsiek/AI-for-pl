module
  proof.WorldCoherent.Right.Source.Frames.NuImprecisionWorldCoherentRightSourceNarrowFrameContextDef
  where

-- File Charter:
--   * Defines source narrowing framing with the target-only context and store
--     lineage witnesses exposed.
--   * Reuses the existing complete catch-up carrier and adds only flat
--     equality and prefix evidence.
--   * Contains no implementation, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad DGG import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Coercions using (Coercion; Inert)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; RuntimeOK; Term; Value; _⟨_⟩)
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (applyRightImpCtxChanges)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (resultCtx; resultStore; targetTailChanges; weakIndexedResult)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )


WorldCoherentRightSourceNarrowFrameContextᵀ : Set₁
WorldCoherentRightSourceNarrowFrameContextᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {A B B′ : Ty} {c : Coercion} {μ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WorldCoherent ρ⁺ →
  SourceNameExclusive Φ →
  AssumptionMembershipUnique Φ →
  StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
  RuntimeOK M′ →
  Value M →
  No• M →
  Inert c →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊒ B →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ₀ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B′ ∶ p →
  (inner : WorldCoherentRightValueCatchupIndexedResult
    {V = M} {M′ = M′} {ρ = ρ⁺} p) →
  resultCtx
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))
    ≡
    applyRightImpCtxChanges
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult inner))))
      Φ →
  RightOnlyStoreImpPrefix
    (lineageStore (worldRightCatchupStoreLineage inner))
    (resultStore
      (weakIndexedResult
        (rightCatchupIndexedResult
          (worldRightCatchupResult inner)))) →
  Σ[ framed ∈
    WorldCoherentRightValueCatchupIndexedResult
      {V = M ⟨ c ⟩} {M′ = M′} {ρ = ρ⁺} q ]
    (resultCtx
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult framed)))
      ≡
      applyRightImpCtxChanges
        (targetTailChanges
          (weakIndexedResult
            (rightCatchupIndexedResult
              (worldRightCatchupResult framed))))
        Φ)
    ×
    RightOnlyStoreImpPrefix
      (lineageStore (worldRightCatchupStoreLineage framed))
      (resultStore
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult framed))))
