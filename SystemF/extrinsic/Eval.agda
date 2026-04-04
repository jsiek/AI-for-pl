module extrinsic.Eval where

-- File Charter:
--   * Fuel-bounded evaluator for closed extrinsic System F terms.
--   * Produces an explicit reduction sequence using `progress` and
--     `preservation`.
--   * Stops once a value is reached or when fuel runs out.

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([])
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import extrinsic.Reduction
open import extrinsic.Progress
open import extrinsic.Preservation

------------------------------------------------------------------------
-- Evaluation result
------------------------------------------------------------------------

record EvalResult (M : Term) : Set where
  constructor result
  field
    term  : Term
    trace : M —↠ term
    value : Value term

open EvalResult public

------------------------------------------------------------------------
-- Fuel-bounded evaluation
------------------------------------------------------------------------

eval :
  ∀ {Δ} {M : Term} {A : Ty} →
  ℕ →
  Δ ⊢ [] ⊢ M ⦂ A →
  Maybe (EvalResult M)
eval {M = M} zero hM with progress hM
... | done v = just (result M (M ∎) v)
... | step _ = nothing
eval {M = M} (suc gas) hM with progress hM
... | done v = just (result M (M ∎) v)
... | step {N = N} M→N with eval gas (preservation hM M→N)
...   | nothing = nothing
...   | just (result K N—↠K vK) =
      just (result K (M —→⟨ M→N ⟩ N—↠K) vK)
