{-# OPTIONS --cumulativity --omega-in-omega #-}
module curry.Parametricity where

-- File Charter:
--   * Public fundamental-theorem interface for curry System F.
--   * Delegates logical-relation compatibility proofs to `curry.proof.Parametricity`.

open import curry.Terms
open import curry.LogicalRelation

import curry.proof.Parametricity as ParametricityProof

fundamental : ∀ {Δ Γ A} (M : Term) → Δ ⊢ Γ ⊢ M ⦂ A → Γ ⊨ M ≈ M ⦂ A
fundamental = ParametricityProof.fundamental
