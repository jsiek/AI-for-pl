module Eval where

-- File Charter:
--   * Fuel-bounded semi-decision procedure for Nu GTSF evaluation to a value.
--   * Iterates `NuReduction` store-change steps using `proof.NuProgress`.
--   * Uses `proof.NuPreservation` to carry typing, store well-formedness, and
--     the runtime-bullet invariant across recursive calls.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)

open import Types
open import NuStore using (StoreWf)
open import NuTerms
open import NuReduction
open import proof.NuProgress using (done; step; crash; progress)
open import proof.NuPreservation
  using (preservation; runtime-preservation; store-preservation)

------------------------------------------------------------------------
-- Successful evaluation result
------------------------------------------------------------------------

record EvalResult (Δ : TyCtx) (Σ : Store) (M : Term) (A : Ty) : Set₁ where
  constructor result
  field
    changes : StoreChanges
    term    : Term
    trace   : M —↠[ changes ] term
    typing  :
      applyTyCtxs changes Δ ∣ applyStores changes Σ ∣ []
        ⊢ term ⦂ applyTys changes A
    value   : Value term

open EvalResult public

------------------------------------------------------------------------
-- Fuel-bounded semi-decision procedure
------------------------------------------------------------------------

eval :
  ∀ {Δ : TyCtx}{Σ : Store}{M : Term}{A : Ty} →
  (gas : ℕ) →
  StoreWf Δ Σ →
  RuntimeOK M →
  Δ ∣ Σ ∣ [] ⊢ M ⦂ A →
  Maybe (EvalResult Δ Σ M A)
eval {M = M} zero wfΣ okM M⊢ with progress okM M⊢
eval {M = M} zero wfΣ okM M⊢ | done vM =
  just (result [] M ↠-refl M⊢ vM)
eval {M = M} zero wfΣ okM M⊢ | step M→N = nothing
eval {M = M} zero wfΣ okM M⊢ | crash refl = nothing
eval {M = M} (suc gas) wfΣ okM M⊢ with progress okM M⊢
eval {M = M} (suc gas) wfΣ okM M⊢ | done vM =
  just (result [] M ↠-refl M⊢ vM)
eval {M = M} (suc gas) wfΣ okM M⊢ | crash refl = nothing
eval {M = M} (suc gas) wfΣ okM M⊢
    | step {χ = χ} {N = N} M→N
    with eval gas
      (store-preservation wfΣ M⊢ M→N)
      (runtime-preservation wfΣ okM M⊢ M→N)
      (preservation wfΣ okM M⊢ M→N)
eval {M = M} (suc gas) wfΣ okM M⊢
    | step {χ = χ} {N = N} M→N | nothing =
  nothing
eval {M = M} (suc gas) wfΣ okM M⊢
    | step {χ = χ} {N = N} M→N
    | just (result χs V N↠V V⊢ vV) =
  just (result (χ ∷ χs) V (↠-step M→N N↠V) V⊢ vV)
