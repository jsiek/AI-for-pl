module
  proof.NuImprecisionRightSourceAllAllocationPrefixProof
  where

-- File Charter:
--   * Proves structural descent through an allocation prefix beneath a
--     source-only binder.
--   * Factors the lifted prefix back to the base world, composes the ambient
--     prefix, and invokes the recursive source-universal closing capability.
--   * Contains no recursive knot, result/view/outcome type, postulate, hole,
--     permissive option, termination bypass, or broad simulation import.

open import Data.Product using (_,_)
open import
  proof.NuImprecisionLeftLiftedStorePrefixFactorLemma
  using (left-lifted-store-prefix-factorᵀ)
open import
  proof.NuImprecisionRightSourceAllAllocationPrefixDef
  using (WorldCoherentRightSourceAllAllocationPrefixᵀ)
open import proof.NuImprecisionStorePrefix using
  (store-imp-prefix-transⁱ)
open import
  proof.NuImprecisionWorldCoherentRightSourceAllClosingDef
  using (WorldCoherentRightSourceAllClosingᵀ)


world-coherent-right-source-all-allocation-prefix-proofᵀ :
  WorldCoherentRightSourceAllClosingᵀ →
  WorldCoherentRightSourceAllAllocationPrefixᵀ
world-coherent-right-source-all-allocation-prefix-proofᵀ
    close prefix coherent exclusive unique wfR okN′ vV noV
    liftρ liftγ prefixᴸ inner
    with left-lifted-store-prefix-factorᵀ liftρ prefixᴸ
world-coherent-right-source-all-allocation-prefix-proofᵀ
    close prefix coherent exclusive unique wfR okN′ vV noV
    liftρ liftγ prefixᴸ inner
    | ρ₋ , prefix₋ , lift₋ =
  close (store-imp-prefix-transⁱ prefix₋ prefix)
    coherent exclusive unique wfR okN′ vV noV lift₋ liftγ inner
