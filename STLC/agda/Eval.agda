module Eval where

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)

open import STLC
open import TypeSafety using (ProgressResult; pr-done; pr-step; progress_top; preservation)

------------------------------------------------------------------------
-- Evaluation results
------------------------------------------------------------------------

record EvalResult (M : Term) : Set where
  constructor result
  field
    term  : Term
    trace : M —↠ term
    value : Value term

open EvalResult public

------------------------------------------------------------------------
-- Fuel-bounded evaluator
------------------------------------------------------------------------

eval :
  ∀ {M : Term} {A : Ty} ->
  ℕ ->
  HasType [] M A ->
  Maybe (EvalResult M)
eval {M = M} zeroℕ hM with progress_top hM
eval {M = M} zeroℕ hM | pr-done v = just (result M (ms-refl M) v)
eval {M = M} zeroℕ hM | pr-step _ = nothing
eval {M = M} (sucℕ gas) hM with progress_top hM
eval {M = M} (sucℕ gas) hM | pr-done v = just (result M (ms-refl M) v)
eval {M = M} (sucℕ gas) hM | pr-step {N = N} s with eval gas (preservation hM s)
eval {M = M} (sucℕ gas) hM | pr-step {N = N} s | nothing = nothing
eval {M = M} (sucℕ gas) hM | pr-step {N = N} s | just (result K N—↠K vK) =
  just (result K (ms-step M s N—↠K) vK)
