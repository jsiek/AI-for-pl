module proof.NuImprecisionClosedNuDGGCounterexample where

-- File Charter:
--   * Refutes `ClosedNuDGG` using the shared concrete
--     source-`gen`/target-`untag` counterexample.
--   * Keeps the contradiction theorem as a direct consumer of the flat core.
--   * Introduces no record, result, view, theorem alias, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import NuReduction using
  ( StoreChanges
  ; keep
  ; ↠-refl
  ; ↠-step
  ; _—↠[_]_
  )
open import NuTerms using
  ( Term
  ; Value
  )
open import proof.NuDGGSpine using (ClosedNuDGG)
open import proof.NuImprecisionGenUntagCounterexampleCore using
  ( V
  ; W
  ; final-relation-impossible
  ; initial-relation
  ; source-runtime
  ; target-runtime
  ; target-trace
  ; vV
  ; vW
  )
open import proof.NuReductionDeterminism using
  (source-blame-excludes-value; value-irreducible)


private
  value-multistep-refl :
    ∀ {U N : Term} {χs : StoreChanges} →
    Value U →
    U —↠[ χs ] N →
    (χs ≡ []) × (N ≡ U)
  value-multistep-refl vU ↠-refl = refl , refl
  value-multistep-refl vU (↠-step U→L L↠N) =
    ⊥-elim (value-irreducible vU U→L)


closed-nu-dgg-counterexample : ClosedNuDGG → ⊥
closed-nu-dgg-counterexample dgg
    with dgg source-runtime target-runtime initial-relation
closed-nu-dgg-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    with backward W (keep ∷ []) target-trace vW
closed-nu-dgg-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    | inj₁ (U , χs , Φ , ρ , r , V↠U , vU , left-eq , right-eq , U⊑W)
    with value-multistep-refl vV V↠U
closed-nu-dgg-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    | inj₁ (U , .[] , Φ , ρ , r , V↠U , vU , left-eq , right-eq , U⊑W)
    | refl , refl =
  final-relation-impossible U⊑W
closed-nu-dgg-counterexample dgg
    | forward , source-divergence , backward , target-divergence
    | inj₂ (χs , V↠blame) =
  source-blame-excludes-value V↠blame ↠-refl vV
