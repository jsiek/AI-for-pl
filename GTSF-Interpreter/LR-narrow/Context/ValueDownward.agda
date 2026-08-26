module LR-narrow.Context.ValueDownward where

-- File Charter:
--   * Proves one-step downward closure of imprecision-indexed values.
--   * Descends through the recursive payload in the active `id★` clause.
--   * Treats the remaining provisional clauses through endpoint certificates.
--   * Contains exactly one exported theorem.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import ImprecisionWf
open import Interpreter using (Value)
open import LR-narrow.Context.AssumptionDownward
open import LR-narrow.LogicalRelation using (ValueNarrowing)
open import LR-narrow.World using (Interpretation; World)
open import Types using (Ty; TyCtx)

value-narrowing-downward : ∀
    {Φ Δᴸ Δᴿ A A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {w : World} {I : Interpretation w} {k : ℕ} {V V′ : Value}
  → ValueNarrowing p I (suc k) V V′
  → ValueNarrowing p I k V V′
value-narrowing-downward {p = id★} {k = zero}
    (endpoints , shape , payload) =
  endpoints
value-narrowing-downward {p = idˣ _ _ _} {k = zero}
    (endpoints , related) =
  endpoints
value-narrowing-downward {p = idι} {k = zero} (endpoints , same) =
  endpoints
value-narrowing-downward {p = p ↦ q} {k = zero}
    (endpoints , related) =
  endpoints
value-narrowing-downward {p = ∀ⁱ p} {k = zero}
    (endpoints , related) =
  endpoints
value-narrowing-downward {p = tag ι} {k = zero} endpoints = endpoints
value-narrowing-downward {p = tag p ⇛ q} {k = zero} endpoints = endpoints
value-narrowing-downward {p = tagˣ _ _} {k = zero}
    (endpoints , related) =
  endpoints
value-narrowing-downward {p = ν nonvar occurs p} {k = zero}
    (endpoints , related) =
  endpoints
value-narrowing-downward {p = id★} {k = suc k}
    (endpoints , shape , payload) =
  endpoints , shape , value-narrowing-downward payload
value-narrowing-downward {p = idˣ _ _ _} {k = suc k}
    (endpoints , related) =
  endpoints , assumption-related-downward related
value-narrowing-downward {p = idι} {k = suc k} related = related
value-narrowing-downward {p = p ↦ q} {k = suc k}
    (endpoints , head , tail) =
  endpoints , tail
value-narrowing-downward {p = ∀ⁱ p} {k = suc k}
    (endpoints , head , tail) =
  endpoints , tail
value-narrowing-downward {p = tag ι} {k = suc k} endpoints = endpoints
value-narrowing-downward {p = tag p ⇛ q} {k = suc k} endpoints = endpoints
value-narrowing-downward {p = tagˣ _ _} {k = suc k}
    (endpoints , related) =
  endpoints , assumption-related-downward related
value-narrowing-downward {p = ν nonvar occurs p} {k = suc k}
    (endpoints , head , tail) =
  endpoints , tail
