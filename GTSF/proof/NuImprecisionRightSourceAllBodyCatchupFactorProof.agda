module
  proof.NuImprecisionRightSourceAllBodyCatchupFactorProof
  where

-- File Charter:
--   * Proves source-universal body catch-up factorization from contextual
--     right-value catch-up.
--   * Reuses contextual body catch-up for the canonical final context and
--     the caught-result factor for all store lineage and base invariants.
--   * Contains no closing proof, recursive dispatcher, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import NuReduction using (applyTyCtxs)
open import
  proof.NuImprecisionRightSourceAllBodyCatchupContextProof
  using (world-coherent-right-source-all-body-catchup-context-proofᵀ)
open import
  proof.NuImprecisionRightSourceAllBodyCatchupFactorDef
  using (WorldCoherentRightSourceAllBodyCatchupFactorᵀ)
open import
  proof.NuImprecisionRightSourceOnlyCaughtFactorLemma
  using (right-source-only-caught-factorᵀ)
open import proof.NuImprecisionRightValueCatchupResultDef using
  ( rightCatchupIndexedResult
  ; rightCatchupSourceChangesEmpty
  )
open import proof.NuImprecisionSimulationResultDef using
  ( sourceChanges
  ; sourceCtxResult
  ; weakIndexedResult
  )
open import
  proof.NuImprecisionWorldCoherentRightCatchupResultDef
  using (worldRightCatchupResult)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupContextDef
  using (WorldCoherentRightValueCatchupContextᵀ)


world-coherent-right-source-all-body-catchup-factor-proofᵀ :
  WorldCoherentRightValueCatchupContextᵀ →
  WorldCoherentRightSourceAllBodyCatchupFactorᵀ
world-coherent-right-source-all-body-catchup-factor-proofᵀ
    catchup {Δᴸ = Δᴸ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    with
      world-coherent-right-source-all-body-catchup-context-proofᵀ
        catchup prefix coherent exclusive unique wfR
        okN′ vV noV liftρ body
world-coherent-right-source-all-body-catchup-factor-proofᵀ
    catchup {Δᴸ = Δᴸ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    | ρ⁺ᴸ , lift⁺ , prefixᴸ ,
      caught , context-eq , right-prefix
    with right-source-only-caught-factorᵀ
      lift⁺ caught context-eq empty-eq left-eq right-prefix
  where
  result =
    weakIndexedResult
      (rightCatchupIndexedResult
        (worldRightCatchupResult caught))

  empty-eq =
    rightCatchupSourceChangesEmpty
      (worldRightCatchupResult caught)

  left-eq =
    trans
      (sourceCtxResult result)
      (cong
        (λ χs → applyTyCtxs χs (suc Δᴸ))
        empty-eq)
world-coherent-right-source-all-body-catchup-factor-proofᵀ
    catchup {Δᴸ = Δᴸ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    | ρ⁺ᴸ , lift⁺ , prefixᴸ ,
      caught , context-eq , right-prefix
    | Δᴿ⁺ , ρlineage , ρbase , ρlift ,
      right-eq , store-eq , embedding , prefix-base ,
      lift-base , coherent-base , exclusive-base ,
      unique-base , wfR-base =
  ρ⁺ᴸ , lift⁺ , prefixᴸ , caught ,
  context-eq , left-eq ,
  Δᴿ⁺ , ρlineage , ρbase , ρlift ,
  right-eq , store-eq , embedding , prefix-base ,
  lift-base , coherent-base , exclusive-base ,
  unique-base , wfR-base
  where
  result =
    weakIndexedResult
      (rightCatchupIndexedResult
        (worldRightCatchupResult caught))

  empty-eq =
    rightCatchupSourceChangesEmpty
      (worldRightCatchupResult caught)

  left-eq =
    trans
      (sourceCtxResult result)
      (cong
        (λ χs → applyTyCtxs χs (suc Δᴸ))
        empty-eq)
