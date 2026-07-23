module
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupContextProof
  where

-- File Charter:
--   * Proves contextual source-universal body catch-up from contextual
--     right-value catch-up in the lifted ambient world.
--   * Uses target/right and source/left context-action commutation to expose
--     the final canonical source-only head.
--   * Contains no closing proof, recursive dispatcher, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Data.Product using (_,_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (rightStoreⁱ-lift-left)
open import Relation.Binary.PropositionalEquality using
  (subst; sym; trans)

open import proof.NuCore.Relations.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-source)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.Right.Core.NuImprecisionRightContextAction using
  (right-context-action-source-only)
open import proof.Right.ValueCatchup.NuImprecisionRightValueCatchupResultDef using
  (rightCatchupIndexedResult)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  (targetTailChanges; weakIndexedResult)
open import
  proof.Right.SourceAll.Bodies.NuImprecisionRightSourceAllBodyCatchupContextDef
  using (WorldCoherentRightSourceAllBodyCatchupContextᵀ)
open import proof.Store.Prefix.NuImprecisionStorePrefixLiftLemma using
  (left-store-prefix-liftᵀ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceProof using
  (world-coherent-lift-left-store)
open import
  proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightValueCatchupContextDef
  using (WorldCoherentRightValueCatchupContextᵀ)
open import proof.WorldCoherent.Right.Value.Catchup.NuImprecisionWorldCoherentRightCatchupResultDef using
  (worldRightCatchupResult)


world-coherent-right-source-all-body-catchup-context-proofᵀ :
  WorldCoherentRightValueCatchupContextᵀ →
  WorldCoherentRightSourceAllBodyCatchupContextᵀ
world-coherent-right-source-all-body-catchup-context-proofᵀ
    catchup {Φ = Φ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    with left-store-prefix-liftᵀ prefix liftρ
world-coherent-right-source-all-body-catchup-context-proofᵀ
    catchup {Φ = Φ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    | ρ⁺ᴸ , lift⁺ , prefixᴸ
    with catchup prefixᴸ
      (world-coherent-lift-left-store lift⁺ coherent)
      (source-name-exclusive-source-only-head exclusive)
      (assumption-membership-unique-source unique)
      (subst (StoreWf _) (sym (rightStoreⁱ-lift-left lift⁺)) wfR)
      okN′ vV noV body
world-coherent-right-source-all-body-catchup-context-proofᵀ
    catchup {Φ = Φ}
    prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    | ρ⁺ᴸ , lift⁺ , prefixᴸ
    | caught , context-eq , right-prefix =
  ρ⁺ᴸ , lift⁺ , prefixᴸ , caught ,
  trans context-eq
    (right-context-action-source-only
      (targetTailChanges
        (weakIndexedResult
          (rightCatchupIndexedResult
            (worldRightCatchupResult caught))))
      Φ) ,
  right-prefix
