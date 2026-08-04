module proof.NuCore.Relations.NuImprecisionConversionAbsenceIdentityDef where

-- File Charter:
--   * Defines the mutual conversion facts that revealing a name absent from
--     the source, or concealing a name absent from the target, is type-level
--     identity.
--   * Exposes the exact source/target polarity needed by the paired-`Lambda`
--     final-reveal closing branch.
--   * Contains no implementation, postulate, hole, permissive option,
--     imprecision, store relation, term relation, or simulation import.

open import Agda.Builtin.Equality using (_≡_)
open import Conversion using (ConcealConversion; RevealConversion)
open import Data.Bool using (false)
open import Types using (occurs)


RevealAbsentSourceIdentityᵀ : Set
RevealAbsentSourceIdentityᵀ =
  ∀ {μ Δ Σ α C c A B} →
  occurs α A ≡ false →
  RevealConversion μ Δ Σ α C c A B →
  A ≡ B


ConcealAbsentTargetIdentityᵀ : Set
ConcealAbsentTargetIdentityᵀ =
  ∀ {μ Δ Σ α C c A B} →
  occurs α B ≡ false →
  ConcealConversion μ Δ Σ α C c A B →
  A ≡ B
