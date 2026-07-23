module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyCaughtFactorProof
  where

-- File Charter:
--   * Proves factorization of completed right-value catch-up beneath a
--     source-only store lift.
--   * Inverts target-only lineage through the lift, factors its allocation
--     prefix, and recovers all final base-world invariants.
--   * Contains no recursive dispatcher, result/view/outcome hierarchy,
--     postulate, hole, permissive option, termination bypass, or broad
--     simulation import.

open import Data.Product using (_,_)
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.PropositionalEquality using (refl; subst)

open import NuStore using (StoreWf)
open import NuTermImprecision using (rightStoreⁱ-lift-left)
open import
  proof.Left.LiftedStore.NuImprecisionLeftLiftedRightRelStoreEmbeddingFactorLemma
  using (left-lifted-right-rel-store-embedding-factorᵀ)
open import
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyCaughtFactorDef
  using (RightSourceOnlyCaughtFactorᵀ)
open import
  proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefixLeftLiftFactorLemma
  using (right-only-store-prefix-left-lift-factorᵀ)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( resultRightCtx
  ; resultStore
  ; weakIndexedResult
  )
open import proof.Source.Core.NuImprecisionSourceOnlyContextDrop using
  ( assumption-membership-unique-drop-source-only
  ; source-name-exclusive-drop-source-only
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (lineageEmbedding)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDropLeftStoreLemma
  using (world-coherence-drop-left-storeᵀ)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef
  using
  ( worldRightCatchupAssumptionMembershipUnique
  ; worldRightCatchupCoherence
  ; worldRightCatchupResult
  ; worldRightCatchupSourceNameExclusive
  ; worldRightCatchupStoreLineage
  ; worldRightCatchupTargetStoreWf
  )


right-source-only-caught-factor-proofᵀ :
  RightSourceOnlyCaughtFactorᵀ
right-source-only-caught-factor-proofᵀ
    liftρ caught refl refl refl right-prefix
    with left-lifted-right-rel-store-embedding-factorᵀ
      liftρ
      (lineageEmbedding
        (worldRightCatchupStoreLineage caught))
right-source-only-caught-factor-proofᵀ
    liftρ caught refl refl refl right-prefix
    | ρlineage , lift-lineage , embedding
    with right-only-store-prefix-left-lift-factorᵀ
      lift-lineage right-prefix
right-source-only-caught-factor-proofᵀ
    liftρ caught refl refl refl right-prefix
    | ρlineage , lift-lineage , embedding
    | ρbase , right-prefix-base , lift-base =
  resultRightCtx result ,
  ρlineage , ρbase , resultStore result ,
  refl , HE.refl ,
  embedding , right-prefix-base , lift-base ,
  world-coherence-drop-left-storeᵀ
    lift-base (worldRightCatchupCoherence caught) ,
  source-name-exclusive-drop-source-only
    (worldRightCatchupSourceNameExclusive caught) ,
  assumption-membership-unique-drop-source-only
    (worldRightCatchupAssumptionMembershipUnique caught) ,
  subst
    (StoreWf (resultRightCtx result))
    (rightStoreⁱ-lift-left lift-base)
    (worldRightCatchupTargetStoreWf caught)
  where
  result =
    weakIndexedResult
      (rightCatchupIndexedResult
        (worldRightCatchupResult caught))
