module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyCaughtFactorDef
  where

-- File Charter:
--   * Defines factorization of a completed right-value catch-up whose initial
--     and final worlds both have a canonical source-only store lift.
--   * Exposes the base target-only lineage, residual allocation prefix, final
--     lift, and every base-world invariant needed by source framing.
--   * Contains no implementation, recursive dispatcher, result/view/outcome
--     hierarchy, postulate, hole, permissive option, or broad simulation
--     import.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Data.Product using (_×_; Σ-syntax)
import Relation.Binary.HeterogeneousEquality as HE

open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (LiftLeftStoreⁱ; StoreImp; rightStoreⁱ)
open import NuTerms using (Term)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (νᵢᶜ)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.Store.RelEmbedding.NuImprecisionRelStoreEmbeddingDef using
  (RelStoreEmbeddingⁱ)
open import proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix using
  (RightOnlyStoreImpPrefix)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; weakIndexedResult
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (lineageStore)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( WorldCoherentRightValueCatchupIndexedResult
  ; worldRightCatchupResult
  ; worldRightCatchupStoreLineage
  )
open import proof.Core.Properties.ReductionProperties using (applyTyVars)


RightSourceOnlyCaughtFactorᵀ : Set₁
RightSourceOnlyCaughtFactorᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴸ : StoreImp (νᵢᶜ Φ) (suc Δᴸ) Δᴿ}
    {V M′ : Term} {A B : Ty}
    {p : νᵢᶜ Φ ∣ suc Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  (liftρ : LiftLeftStoreⁱ (νᵢᶜ Φ) ρ ρᴸ) →
  (caught :
    WorldCoherentRightValueCatchupIndexedResult
      {V = V} {M′ = M′} {ρ = ρᴸ} p) →
  let result =
        weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))
  in
  resultCtx result ≡ νᵢᶜ Ψ →
  sourceChanges result ≡ [] →
  resultLeftCtx result ≡ suc Δᴸ →
  RightOnlyStoreImpPrefix
    (lineageStore
      (worldRightCatchupStoreLineage caught))
    (resultStore result) →
  Σ[ Δᴿ⁺ ∈ TyCtx ]
  Σ[ ρlineage ∈ StoreImp Ψ Δᴸ Δᴿ⁺ ]
  Σ[ ρbase ∈ StoreImp Ψ Δᴸ Δᴿ⁺ ]
  Σ[ ρlift ∈ StoreImp (νᵢᶜ Ψ) (suc Δᴸ) Δᴿ⁺ ]
    resultRightCtx result ≡ Δᴿ⁺
    ×
    HE._≅_ (resultStore result) ρlift
    ×
    RelStoreEmbeddingⁱ
      (applyTyVars [])
      (applyTyVars (targetTailChanges result))
      ρ ρlineage
    ×
    RightOnlyStoreImpPrefix ρlineage ρbase
    ×
    LiftLeftStoreⁱ (νᵢᶜ Ψ) ρbase ρlift
    ×
    WorldCoherent ρbase
    ×
    SourceNameExclusive Ψ
    ×
    AssumptionMembershipUnique Ψ
    ×
    StoreWf Δᴿ⁺ (rightStoreⁱ ρbase)
