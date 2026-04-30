module extrinsic.Progress where

-- File Charter:
--   * Public progress theorem surface for extrinsic System F.
--   * Re-exports supporting canonical-forms and progress witness definitions.

open import Data.List using ([])

open import extrinsic.Reduction
open import extrinsic.proof.Progress public hiding (progress)
import extrinsic.proof.Progress as ProgressProof

progress :
  ∀ {Δ : TyCtx} {M : Term} {A : Ty} →
  Δ ∣ [] ⊢ M ⦂ A →
  Progress M
progress = ProgressProof.progress
