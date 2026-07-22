module proof.NuImprecisionTargetTagCancellationCounterexample where

-- File Charter:
--   * Refutes generic target-tag cancellation using the shared concrete
--     source-`gen`/target-`untag` counterexample.
--   * Keeps the contradiction theorem as a direct consumer of the flat core.
--   * Introduces no record, result, view, theorem alias, postulate, hole, or
--     permissive option.

open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import proof.NuImprecisionGenUntagCounterexampleCore using
  ( V-tagged-relation
  ; exclusive₀
  ; final-relation-impossible
  ; gG
  ; noV
  ; q
  ; unique₀
  ; vV
  ; vW
  )
open import proof.NuImprecisionTargetTagCancellationDef using
  (TargetTagCancellationᵀ)


target-tag-cancellation-counterexample :
  TargetTagCancellationᵀ →
  ⊥
target-tag-cancellation-counterexample cancel
    with cancel exclusive₀ unique₀ gG vV noV vW
      V-tagged-relation q
target-tag-cancellation-counterexample cancel
    | G≡G , canceled =
  final-relation-impossible canceled
