module curry.TypeSafety where

-- File Charter:
--   * Public type-safety interface for curry System F.
--   * Re-exports the `Safety` record and helper wrappers.
--   * Keeps theorem statements thin and trust-facing.

open import Data.Product using (∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.List using ([])

open import curry.Reduction

import curry.proof.TypeSafety as TypeSafetyProof

open TypeSafetyProof public using (Safety; typeSafety; typeSafety-↠)

type-safety :
  ∀ {Δ : TyCtx} {M N : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  M —↠ N →
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety = TypeSafetyProof.type-safety
