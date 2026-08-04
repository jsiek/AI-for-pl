module proof.Target.FunctionCast.NuImprecisionTargetFunctionCastSpineMeasureDef where

-- File Charter:
--   * Defines the well-founded rank for nested inert casts on a target value.
--   * Counts value-cast constructors and ignores coercion size because each
--     target `β-↦` removes exactly one outer function cast.
--   * Contains no recursion theorem, postulate, hole, or permissive option.

open import Data.Nat using (ℕ; suc; zero)

open import NuTerms using (Term; Value; ƛ_; Λ_; $; _⟨_⟩)


targetFunctionCastSpineRank : ∀ {V : Term} → Value V → ℕ
targetFunctionCastSpineRank (ƛ N) = zero
targetFunctionCastSpineRank (Λ vV) =
  targetFunctionCastSpineRank vV
targetFunctionCastSpineRank ($ k) = zero
targetFunctionCastSpineRank (vV ⟨ inert ⟩) =
  suc (targetFunctionCastSpineRank vV)
