module LR-narrow.Context.ValueFuture where

-- File Charter:
--   * Proves future-world monotonicity of imprecision-indexed values.
--   * Delegates each structural clause to its one-theorem support module.
--   * Weakens both tag agreement and recursive payloads for active `id★`.
--   * Treats the remaining provisional clauses through existing evidence.

open import Agda.Builtin.Equality using (refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)

open import ImprecisionWf
open import Interpreter using (Value)
open import LR-narrow.Context.AssumptionFuture
open import LR-narrow.Context.FunctionsFuture
open import LR-narrow.Context.GroundTagAgreementFuture
open import LR-narrow.Context.RightUniversalsFuture
open import LR-narrow.Context.TypedEndpointsFuture
open import LR-narrow.Context.UniversalsFuture
open import LR-narrow.Dynamic
open import LR-narrow.LogicalRelation using (ValueNarrowing)
open import LR-narrow.World
open import Types using (Ty; TyCtx)

value-narrowing-future : ∀
    {Φ Δᴸ Δᴿ A A′} {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {current future : World}
    {I : Interpretation {Φ} {Δᴸ} {Δᴿ} current}
    {J : Interpretation {Φ} {Δᴸ} {Δᴿ} future}
    {k : ℕ} {V V′ : Value}
  → J ⊒ⁱ I
  → ValueNarrowing p I k V V′
  → ValueNarrowing p J k V V′
value-narrowing-future {k = zero} J⊒I endpoints =
  typed-endpoints-future J⊒I endpoints
value-narrowing-future {p = id★} {k = suc k} J⊒I
    (endpoints , shape , payload) =
  typed-endpoints-future J⊒I endpoints ,
  dynamic-payload-shape
    (precise-ground shape)
    (imprecise-ground shape)
    (precise-ground-proof shape)
    (imprecise-ground-proof shape)
    (dynamic-left-types shape)
    (dynamic-right-types shape)
    (dynamic-left-payload shape)
    (dynamic-right-payload shape)
    (dynamic-left-shape shape)
    (dynamic-right-shape shape)
    (payload-imprecision shape)
    (ground-tag-agreement-future J⊒I (payload-tags-agree shape)) ,
  value-narrowing-future J⊒I payload
value-narrowing-future {p = idˣ assumption∈ X< Y<} {k = suc k}
    J⊒I@(future-interpretation growth left-eq right-eq refl)
    (endpoints , related) =
  typed-endpoints-future J⊒I endpoints ,
  assumption-related-future J⊒I related
value-narrowing-future {p = idι} {k = suc k} J⊒I
    (endpoints , same) =
  typed-endpoints-future J⊒I endpoints , same
value-narrowing-future {p = p ↦ q} {k = suc k} J⊒I
    (endpoints , related) =
  typed-endpoints-future J⊒I endpoints ,
  functions-related-future J⊒I related
value-narrowing-future {p = ∀ⁱ p} {k = suc k} J⊒I
    (endpoints , related) =
  typed-endpoints-future J⊒I endpoints ,
  universals-related-future J⊒I related
value-narrowing-future {p = tag ι} {k = suc k} J⊒I endpoints =
  typed-endpoints-future J⊒I endpoints
value-narrowing-future {p = tag p ⇛ q} {k = suc k} J⊒I endpoints =
  typed-endpoints-future J⊒I endpoints
value-narrowing-future {p = tagˣ assumption∈ X<} {k = suc k}
    J⊒I@(future-interpretation growth left-eq right-eq refl)
    (endpoints , related) =
  typed-endpoints-future J⊒I endpoints ,
  assumption-related-future J⊒I related
value-narrowing-future {p = ν nonvar occurs p} {k = suc k} J⊒I
    (endpoints , related) =
  typed-endpoints-future J⊒I endpoints ,
  right-universals-related-future J⊒I related
