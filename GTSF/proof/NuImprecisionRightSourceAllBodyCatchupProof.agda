module proof.NuImprecisionRightSourceAllBodyCatchupProof where

-- File Charter:
--   * Proves that right-value catch-up can recurse under a source-only type
--     binder in a lifted ambient world.
--   * Transports the ambient prefix and every world invariant canonically,
--     returning the existing catch-up result without a new carrier.
--   * Contains no closing/collapse proof, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import Data.Product using (_,_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (rightStoreⁱ-lift-left)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof
  using (assumption-membership-unique-source)
open import proof.NuImprecisionContextExclusivityProof using
  (source-name-exclusive-source-only-head)
open import proof.NuImprecisionRightSourceAllBodyCatchupDef using
  (WorldCoherentRightSourceAllBodyCatchupᵀ)
open import proof.NuImprecisionStorePrefixLiftLemma using
  (left-store-prefix-liftᵀ)
open import proof.NuImprecisionWorldCoherenceProof using
  (world-coherent-lift-left-store)
open import
  proof.NuImprecisionWorldCoherentRightValueCatchupPrefixDef
  using (WorldCoherentRightValueCatchupPrefixᵀ)


world-coherent-right-source-all-body-catchup-proofᵀ :
  WorldCoherentRightValueCatchupPrefixᵀ →
  WorldCoherentRightSourceAllBodyCatchupᵀ
world-coherent-right-source-all-body-catchup-proofᵀ
    catchup prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    with left-store-prefix-liftᵀ prefix liftρ
world-coherent-right-source-all-body-catchup-proofᵀ
    catchup prefix coherent exclusive unique wfR okN′ vV noV
    liftρ body
    | ρ⁺ᴸ , lift⁺ , prefixᴸ =
  ρ⁺ᴸ , lift⁺ , prefixᴸ ,
  catchup prefixᴸ
    (world-coherent-lift-left-store lift⁺ coherent)
    (source-name-exclusive-source-only-head exclusive)
    (assumption-membership-unique-source unique)
    (subst (StoreWf _) (sym (rightStoreⁱ-lift-left lift⁺)) wfR)
    okN′ vV noV body
