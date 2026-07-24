module proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef where

-- File Charter:
--   * Defines the well-founded potential used by joint target-cast, target
--     allocation, and target-bullet normalization.
--   * Charges sequence structure twice and pending frames once so every
--     administrative root has a strict decrease.
--   * States generic strict descent from a nonempty pending list to its tail.
--   * States strict rank growth when an inert cast is absorbed into a value.
--   * States the exact three-successor descent from a paired `Λ` allocation
--     boundary to its inert residual continuation.
--   * States rank invariance when a right allocation shifts every pending
--     coercion under the new target-store binder.
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


targetPendingAdministrationRank :
  ∀ {V : Term} → Value V → List Coercion → ℕ
targetPendingAdministrationRank vV cs =
  2 * (valueAdministrationWeight vV +
    pendingCastAdministrationWeight cs) + length cs


targetNuAdministrationRank :
  ∀ {V : Term} → Value V → Coercion → List Coercion → ℕ
targetNuAdministrationRank vV c cs =
  2 * (valueAdministrationWeight vV + castAdministrationWeight c +
    pendingCastAdministrationWeight cs) + suc (length cs) + 1


TargetPendingAdministrationTailDecreaseᵀ : Set
TargetPendingAdministrationTailDecreaseᵀ =
  ∀ {V} (vV : Value V) c cs →
  targetPendingAdministrationRank vV cs <
    targetPendingAdministrationRank vV (c ∷ cs)


TargetInertValueAdministrationIncreaseᵀ : Set
TargetInertValueAdministrationIncreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  targetPendingAdministrationRank vV cs <
    targetPendingAdministrationRank (vV ⟨ inert-c ⟩) cs


TargetPairedLambdaAllocationContinuationRankDecreaseᵀ : Set
TargetPairedLambdaAllocationContinuationRankDecreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  targetPendingAdministrationRank (Λ vV) (c ∷ cs) ≡
    suc (suc (suc
      (targetPendingAdministrationRank (vV ⟨ inert-c ⟩) cs)))


TargetPendingAdministrationShiftMapRankInvariantᵀ : Set
TargetPendingAdministrationShiftMapRankInvariantᵀ =
  ∀ {V} (vV : Value V) cs →
  targetPendingAdministrationRank vV (map ⇑ᶜ cs) ≡
    targetPendingAdministrationRank vV cs


TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ : Set
TargetPairedLambdaRightAllocationContinuationRankDecreaseᵀ =
  ∀ {V c} (vV : Value V) (inert-c : Inert c) cs →
  targetPendingAdministrationRank (Λ vV) (c ∷ cs) ≡
    suc (suc (suc
      (targetPendingAdministrationRank
        (vV ⟨ inert-c ⟩) (map ⇑ᶜ cs))))
