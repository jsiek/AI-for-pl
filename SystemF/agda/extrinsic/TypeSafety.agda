module extrinsic.TypeSafety where

-- File Charter:
--   * Public type-safety theorem surface for extrinsic System F.
--   * Exposes the final closed-term theorem and supporting safety wrappers.

open import Data.Product using (∃; ∃-syntax)
open import Data.Sum using (_⊎_)
open import Data.List using ([])

open import extrinsic.Reduction
open import extrinsic.proof.TypeSafety public hiding (type-safety)
import extrinsic.proof.TypeSafety as TypeSafetyProof

type-safety :
  ∀ {Δ : TyCtx} {M N : Term} {A : Ty} →
  Δ ∣ [] ⊢ M ⦂ A →
  M —↠ N →
  (∃[ N′ ] (N —→ N′)) ⊎ Value N
type-safety = TypeSafetyProof.type-safety
