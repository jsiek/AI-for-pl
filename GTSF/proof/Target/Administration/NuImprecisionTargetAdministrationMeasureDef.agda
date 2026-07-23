module proof.Target.Administration.NuImprecisionTargetAdministrationMeasureDef where

-- File Charter:
--   * Defines the well-founded potential used by joint target-cast, target
--     allocation, and target-bullet normalization.
--   * Charges sequence structure twice and pending frames once so every
--     administrative root has a strict decrease.
--   * Contains no semantic recursion, theorem proof, postulate, hole, or
--     permissive option.

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _+_; _*_; suc; zero)

open import Coercions using (Coercion; sizeᶜ)
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
