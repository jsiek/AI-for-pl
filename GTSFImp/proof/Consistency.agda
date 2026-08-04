module proof.Consistency where

-- File Charter:
--   * Proves that every closed type is consistent with the dynamic type.
--   * Derives the result from closed-type imprecision and the common-lower
--     characterization of consistency.
--   * Depends on proof.Imprecision and proof.ImprecisionConsistency.

open import Data.Product using (_,_)

open import Types
open import Consistency
open import proof.Imprecision using (imprecise-star)
open import proof.ImprecisionConsistency
  using (common-lower-consistent; refl⊑)

consistent-star : ∀ (A : Ty 0) → A ∼ ★
consistent-star A = common-lower-consistent
  (A , refl⊑ A , imprecise-star A)
