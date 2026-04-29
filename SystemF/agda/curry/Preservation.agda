module curry.Preservation where

-- File Charter:
--   * Public preservation theorem interface for curry System F.
--   * Exposes single-step and multi-step preservation wrappers.
--   * Delegates proof scripts to `curry.proof.Preservation`.

open import curry.Reduction

import curry.proof.Preservation as PreservationProof

preservation :
  {Δ : TyCtx} {Γ : Ctx} {M N : Term} {A : Ty} →
  Δ ⊢ Γ ⊢ M ⦂ A →
  M —→ N →
  Δ ⊢ Γ ⊢ N ⦂ A
preservation = PreservationProof.preservation

multi-preservation :
  {Δ : TyCtx} {Γ : Ctx} {M N : Term} {A : Ty} →
  Δ ⊢ Γ ⊢ M ⦂ A →
  M —↠ N →
  Δ ⊢ Γ ⊢ N ⦂ A
multi-preservation = PreservationProof.multi-preservation
