module
  proof.Target.Administration.NuImprecisionTargetPendingLambdaAllocationTraceDef
  where

-- File Charter:
--   * States the exact target reduction trace for allocating a pending
--     polymorphic lambda beneath an arbitrary hereditary target-cast list.
--   * Exposes the allocation `bind ★`, the following `keep` beta step, and
--     the resulting shift of every pending coercion.
--   * Contains no implementation, simulation result, outcome carrier,
--     postulate, hole, permissive option, or compatibility wrapper.

open import Coercions using (Coercion; ⇑ᶜ)
open import Data.List using (List; []; map; _∷_)
open import NuReduction using (bind; keep; _—↠[_]_)
open import NuTerms using (No•; Term; Value; Λ_; _⟨_⟩; ν)
open import Types using (★)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (applyTargetPendingCasts)


TargetPendingLambdaAllocationTraceᵀ : Set
TargetPendingLambdaAllocationTraceᵀ =
  ∀ {W′ : Term} {s : Coercion} {cs : List Coercion} →
  Value W′ →
  No• W′ →
  applyTargetPendingCasts (ν ★ (Λ W′) s) cs
    —↠[ bind ★ ∷ keep ∷ [] ]
    applyTargetPendingCasts (W′ ⟨ s ⟩) (map ⇑ᶜ cs)
