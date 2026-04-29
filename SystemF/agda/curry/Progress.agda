module curry.Progress where

-- File Charter:
--   * Public progress theorem interface for curry System F.
--   * Re-exports the progress witness type and constructors.
--   * Delegates proof details to `curry.proof.Progress`.

open import curry.Reduction
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.List using ([])

import curry.proof.Progress as ProgressProof

open ProgressProof public using (Progress; done; step)

progress :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ⊢ [] ⊢ M ⦂ A →
  Progress M
progress = ProgressProof.progress
