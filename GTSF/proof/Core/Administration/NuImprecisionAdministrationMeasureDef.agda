module proof.Core.Administration.NuImprecisionAdministrationMeasureDef where

-- File Charter:
--   * Defines the side-neutral well-founded potential used by cast,
--     allocation, and runtime-bullet normalization.
--   * Charges sequence structure twice and pending frames once so every
--     administrative root has a strict decrease.
--   * States generic strict descent from a nonempty pending list to its tail.
--   * States strict rank growth when an inert cast is absorbed into a value.
--   * States the exact three-successor descent from a `Λ` allocation boundary
--     to its inert residual continuation.
--   * States rank invariance when allocation shifts every pending coercion.
--   * Contains no semantic recursion, theorem proof, postulate, hole, or
--     permissive option.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Nat using (ℕ; _+_; _*_; _<_; suc; zero)

open import Coercions using (Coercion; Inert; sizeᶜ; ⇑ᶜ)
open import NuTerms using (Term; Value; ƛ_; Λ_; $; _⟨_⟩)


castAdministrationWeight : Coercion → ℕ
castAdministrationWeight c = suc (2 * sizeᶜ c)


valueAdministrationWeight : ∀ {V : Term} → Value V → ℕ
valueAdministrationWeight (ƛ N) = zero
valueAdministrationWeight (Λ vV) =
  suc (valueAdministrationWeight vV)
valueAdministrationWeight ($ k) = zero
valueAdministrationWeight {V = V ⟨ c ⟩} (vV ⟨ inert-c ⟩) =
  valueAdministrationWeight vV + castAdministrationWeight c


pendingCastAdministrationWeight : List Coercion → ℕ
pendingCastAdministrationWeight [] = zero
pendingCastAdministrationWeight (c ∷ cs) =
  castAdministrationWeight c + pendingCastAdministrationWeight cs


pendingAdministrationRank :
  ∀ {V : Term} → Value V → List Coercion → ℕ
pendingAdministrationRank vV cs =
  2 * (valueAdministrationWeight vV +
    pendingCastAdministrationWeight cs) + length cs


nuAdministrationRank :
  ∀ {V : Term} → Value V → Coercion → List Coercion → ℕ
nuAdministrationRank vV c cs =
  2 * (valueAdministrationWeight vV + castAdministrationWeight c +
    pendingCastAdministrationWeight cs) + suc (length cs) + 1


PendingAdministrationTailDecreaseᵀ : Set
PendingAdministrationTailDecreaseᵀ =
  ∀ {V} (vV : Value V) c cs →
  pendingAdministrationRank vV cs <
    pendingAdministrationRank vV (c ∷ cs)


InertValueAdministrationIncreaseᵀ : Set
InertValueAdministrationIncreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  pendingAdministrationRank vV cs <
    pendingAdministrationRank (vV ⟨ inert-c ⟩) cs


LambdaAllocationContinuationRankDecreaseᵀ : Set
LambdaAllocationContinuationRankDecreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  pendingAdministrationRank (Λ vV) (c ∷ cs) ≡
    suc (suc (suc
      (pendingAdministrationRank (vV ⟨ inert-c ⟩) cs)))


PendingAdministrationShiftMapRankInvariantᵀ : Set
PendingAdministrationShiftMapRankInvariantᵀ =
  ∀ {V} (vV : Value V) cs →
  pendingAdministrationRank vV (map ⇑ᶜ cs) ≡
    pendingAdministrationRank vV cs


LambdaShiftedAllocationContinuationRankDecreaseᵀ : Set
LambdaShiftedAllocationContinuationRankDecreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  pendingAdministrationRank (Λ vV) (c ∷ cs) ≡
    suc (suc (suc
      (pendingAdministrationRank
        (vV ⟨ inert-c ⟩) (map ⇑ᶜ cs))))
