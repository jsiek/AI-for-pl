module extrinsic.Preservation where

-- File Charter:
--   * Public preservation theorem surface for extrinsic System F.
--   * Re-exports private typing/substitution infrastructure used across proofs.

open import extrinsic.Reduction
open import extrinsic.proof.Preservation public hiding (preservation)
import extrinsic.proof.Preservation as PreservationProof

preservation :
  {Δ : TyCtx} {Γ : Ctx} {M N : Term} {A : Ty} →
  Δ ∣ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ∣ Γ ⊢ N ⦂ A
preservation = PreservationProof.preservation
