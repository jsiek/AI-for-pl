module proof.NuImprecisionAssumptionMembershipUniquenessLemma where

-- File Charter:
--   * Instantiates precision-index uniqueness with the canonical fresh-path
--     imprecision transport proof.
--   * Exposes the canonical theorem while keeping its higher-order Def small.
--   * Contains no wrapper carrier, postulate, hole, or permissive option.

open import proof.NuImprecisionAssumptionMembershipUniquenessDef using
  ( AssumptionMembershipUnique
  ; PrecisionIndexUnique
  )
open import proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-uniqueness-proofᵀ)
open import
  proof.NuImprecisionFreshTypePathImprecisionTransportProof using
  (fresh-type-path-imprecision-transport-proof)


assumption-membership-unique→precision-index-unique :
  ∀ {Φ} →
  AssumptionMembershipUnique Φ →
  PrecisionIndexUnique Φ
assumption-membership-unique→precision-index-unique =
  assumption-membership-uniqueness-proofᵀ
    fresh-type-path-imprecision-transport-proof
