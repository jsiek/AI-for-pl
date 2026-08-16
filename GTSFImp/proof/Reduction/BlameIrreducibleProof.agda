module proof.Reduction.BlameIrreducibleProof where

-- File Charter:
--   * Proves irreducibility of blame for store-changing multi-step
--     reduction.
--   * Inverts the first store-changing step locally and exhaustively.
--   * Exports blame-irreducible* as the implementation of the Def interface.

open import Data.Empty using (⊥; ⊥-elim)

open import Types using (TyCtx)
open import CastTerms using (Term; blame)
open import Reduction using
  (StoreChange; keep; bind; _—→[_]_; pure-step; _—↠[_]_; ↠-refl;
   ↠-step)
open import proof.Reduction.BlameIrreducibleDef
  using (BlameIrreducible*ᵀ; blame-trace-refl)


blame-no-step : ∀ {Δ Δ′ : TyCtx} {N : Term Δ′}
    {χ : StoreChange Δ Δ′}
  → blame {Δ} —→[ χ ] N
  → ⊥
blame-no-step {χ = keep} (pure-step ())
blame-no-step {χ = bind R} ()


blame-irreducible* : BlameIrreducible*ᵀ
blame-irreducible* ↠-refl = blame-trace-refl
blame-irreducible* (↠-step step rest) = ⊥-elim (blame-no-step step)
