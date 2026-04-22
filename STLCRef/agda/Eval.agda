module Eval where

-- File Charter:
--   * Public wrapper for STLCRef fuel-bounded configuration evaluation.
--   * Exposes `eval` and `eval-term` while delegating implementation to
--     `proof.Eval`.

open import Agda.Builtin.Maybe using (Maybe)
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Agda.Builtin.List using ([])
open import Data.Product using (∃; ∃-syntax; _,_)

open import STLCRef
import proof.Eval as EvalProof

------------------------------------------------------------------------
-- Fuel-bounded evaluator
------------------------------------------------------------------------

eval : (gas : ℕ) -> (c : Config) -> Maybe (∃[ c′ ] (c —↠ c′))
eval gas c = EvalProof.eval gas c

eval-term : (gas : ℕ) -> (M : Term) -> Maybe (∃[ c′ ] ((M , []) —↠ c′))
eval-term gas M = eval gas (M , [])
