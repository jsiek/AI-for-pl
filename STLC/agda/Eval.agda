module Eval where

-- File Charter:
--   * Public wrapper for STLC fuel-bounded evaluation.
--   * Exposes `eval` while delegating implementation to `proof.Eval`.

open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.Product using (∃; ∃-syntax)

open import STLC
import proof.Eval as EvalProof

------------------------------------------------------------------------
-- Fuel-bounded evaluator
------------------------------------------------------------------------

eval : (gas : ℕ) → (M : Term) → Maybe (∃[ N ] (M —↠ N))
eval gas M = EvalProof.eval gas M
