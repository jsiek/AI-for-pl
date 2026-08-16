module proof.Reduction.ValueIrreducibleDef where

-- File Charter:
--   * States irreducibility of values for store-changing multi-step
--     reduction.
--   * Packages the dependent endpoint indices in constructor form so clients
--     can recover reflexivity by one pattern match and no induction.
--   * Contains no irreducibility proof.

open import Types using (TyCtx)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; []; _—↠[_]_)


data ValueTraceRefl {Δ : TyCtx} (V : Term Δ) :
    ∀ {Δ′} → StoreChanges Δ Δ′ → Term Δ′ → Set where
  value-trace-refl : ValueTraceRefl V [] V


ValueIrreducible*ᵀ : Set
ValueIrreducible*ᵀ =
  ∀ {Δ Δ′} {V : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → Value V
  → V —↠[ χs ] N
  → ValueTraceRefl V χs N
