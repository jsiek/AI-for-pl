module Termination where

-- File Charter:
--   * Public statement of STLC termination.
--   * Logical-relations proof lives in `proof/Termination.agda`.

open import Agda.Builtin.List using ([])
open import Data.Product using (Σ; _×_)
open import STLC

import proof.Termination as Proof

termination :
  {M : Term} {A : Ty} ->
  [] ⊢ M ⦂ A ->
  Σ Term (λ V -> (M —↠ V) × Value V)
termination = Proof.termination
