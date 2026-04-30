{-# OPTIONS --cumulativity --omega-in-omega #-}
module extrinsic.Parametricity where

-- File Charter:
--   * Public parametricity surface for extrinsic System F.
--   * Exposes the fundamental theorem with a thin wrapper around private proofs.

open import extrinsic.Reduction
open import extrinsic.LogicalRelation
open import extrinsic.proof.Parametricity public hiding (fundamental)
import extrinsic.proof.Parametricity as ParametricityProof

fundamental : ∀ {Δ Γ A} (M : Term)
  → Δ ∣ Γ ⊢ M ⦂ A
  → Γ ⊨ M ≈ M ⦂ A
fundamental = ParametricityProof.fundamental
