module proof.Reduction.BlameIrreducibleDef where

-- File Charter:
--   * States irreducibility of blame for store-changing multi-step
--     reduction.
--   * Packages the dependent endpoint indices in constructor form so clients
--     can recover reflexivity by one pattern match and no induction.
--   * Contains no irreducibility proof.

open import Types using (TyCtx)
open import CastTerms using (Term; blame)
open import Reduction using (StoreChanges; []; _—↠[_]_)


data BlameTraceRefl {Δ : TyCtx} :
    ∀ {Δ′} → StoreChanges Δ Δ′ → Term Δ′ → Set where
  blame-trace-refl : BlameTraceRefl [] blame


BlameIrreducible*ᵀ : Set
BlameIrreducible*ᵀ =
  ∀ {Δ Δ′} {N : Term Δ′} {χs : StoreChanges Δ Δ′}
  → blame {Δ} —↠[ χs ] N
  → BlameTraceRefl χs N
