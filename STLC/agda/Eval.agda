module Eval where

open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.List using ([])
open import Agda.Builtin.Nat renaming (Nat to ℕ; zero to zeroℕ; suc to sucℕ)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import STLC
open import TypeSafety using (progress; preservation)

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
  [] ⊢ M ⦂ A ->
  Maybe (EvalResult M)
eval {M = M} zeroℕ hM with progress hM
eval {M = M} zeroℕ hM | inj₂ v = just (result M (M ∎) v)
eval {M = M} zeroℕ hM | inj₁ _ = nothing
eval {M = M} (sucℕ gas) hM with progress hM
eval {M = M} (sucℕ gas) hM | inj₂ v = just (result M (M ∎) v)
eval {M = M} (sucℕ gas) hM | inj₁ (N , s) with eval gas (preservation hM s)
eval {M = M} (sucℕ gas) hM | inj₁ (N , s) | nothing = nothing
eval {M = M} (sucℕ gas) hM | inj₁ (N , s) | just (result K N—↠K vK) =
  just (result K (M —→⟨ s ⟩ N—↠K) vK)
