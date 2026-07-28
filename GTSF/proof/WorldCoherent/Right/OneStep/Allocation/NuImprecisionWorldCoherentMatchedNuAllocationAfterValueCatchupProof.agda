module
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupProof
  where

-- File Charter:
--   * Lifts matched allocation after value catch-up into the world-coherent
--     indexed outcome.
--   * Preserves the exact lower-level result/lineage coupling while extending
--     world coherence, source-name exclusivity, and membership uniqueness.
--   * Contains no dispatcher, postulate, hole, permissive option, or legacy
--     allocation-simulation import.

open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import ImprecisionWf using (ImpCtx)
open import Types using (TyCtx)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessDef
  using (AssumptionMembershipUnique)
open import
  proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-matched)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityDef
  using (SourceNameExclusive)
open import
  proof.NuCore.Relations.NuImprecisionContextExclusivityProof
  using (source-name-exclusive-matched-head)
open import
  proof.OneStep.Allocation.NuImprecisionMatchedNuAllocationAfterValueCatchupDef
  using (MatchedNuAllocationAfterValueCatchupᵀ)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceLemma
  using (world-coherent-matched-allocation)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef
  using (world-indexed-outcome-related)
open import
  proof.WorldCoherent.Right.OneStep.Allocation.NuImprecisionWorldCoherentMatchedNuAllocationAfterValueCatchupDef
  using (WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ)


private
  world-coherent-package :
    (store :
      Σ[ Φ ∈ ImpCtx ]
      Σ[ Δᴸ ∈ TyCtx ]
      Σ[ Δᴿ ∈ TyCtx ]
        StoreImp Φ Δᴸ Δᴿ) →
    Set₁
  world-coherent-package (_ , _ , _ , ρ) = WorldCoherent ρ


  source-exclusive-package :
    (store :
      Σ[ Φ ∈ ImpCtx ]
      Σ[ Δᴸ ∈ TyCtx ]
      Σ[ Δᴿ ∈ TyCtx ]
        StoreImp Φ Δᴸ Δᴿ) →
    Set
  source-exclusive-package (Φ , _ , _ , _) = SourceNameExclusive Φ


  assumption-unique-package :
    (store :
      Σ[ Φ ∈ ImpCtx ]
      Σ[ Δᴸ ∈ TyCtx ]
      Σ[ Δᴿ ∈ TyCtx ]
        StoreImp Φ Δᴸ Δᴿ) →
    Set
  assumption-unique-package (Φ , _ , _ , _) =
    AssumptionMembershipUnique Φ


world-coherent-matched-nu-allocation-after-value-catchup-proofᵀ :
  MatchedNuAllocationAfterValueCatchupᵀ →
  WorldCoherentMatchedNuAllocationAfterValueCatchupᵀ
world-coherent-matched-nu-allocation-after-value-catchup-proofᵀ
    allocation
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′ catchup vW noW
    caught-lineage final-coherent final-exclusive final-unique
    with allocation
      s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′ catchup vW noW
      caught-lineage
world-coherent-matched-nu-allocation-after-value-catchup-proofᵀ
    allocation
    s↑ s′↑ pA A⇑⊑A′⇑ pB replace vV′ noV′ catchup vW noW
    caught-lineage final-coherent final-exclusive final-unique
    | final-indexed , ρ↑ , X , X′ , p ,
      combined-lineage , liftρ⁺ , exact-store =
  world-indexed-outcome-related
    final-indexed
    combined-lineage
    (subst world-coherent-package (sym exact-store)
      (world-coherent-matched-allocation liftρ⁺ final-coherent))
    (subst source-exclusive-package (sym exact-store)
      (source-name-exclusive-matched-head final-exclusive))
    (subst assumption-unique-package (sym exact-store)
      (assumption-membership-unique-matched final-unique))
