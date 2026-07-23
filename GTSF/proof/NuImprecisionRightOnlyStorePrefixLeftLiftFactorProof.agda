module
  proof.NuImprecisionRightOnlyStorePrefixLeftLiftFactorProof
  where

-- File Charter:
--   * Proves target-only prefix factorization across source-only lifts by
--     exhaustive recursion on the target-only prefix.
--   * Copies each target entry to the base store and extends the lift with
--     the corresponding right-only constructor.
--   * Contains no term relation, postulate, hole, catch-all, permissive
--     option, termination bypass, or broad simulation import.

open import Data.List using (_∷_)
open import Data.Product using (_,_)

open import NuTermImprecision using
  (lift-left-store-right; store-right)
open import proof.NuImprecisionRightOnlyStorePrefix using
  ( right-only-prefix-refl
  ; right-only-prefix-right
  )
open import
  proof.NuImprecisionRightOnlyStorePrefixLeftLiftFactorDef
  using (RightOnlyStorePrefixLeftLiftFactorᵀ)


right-only-store-prefix-left-lift-factor-proofᵀ :
  RightOnlyStorePrefixLeftLiftFactorᵀ
right-only-store-prefix-left-lift-factor-proofᵀ
    {ρ = ρ} liftρ right-only-prefix-refl =
  ρ , right-only-prefix-refl , liftρ
right-only-store-prefix-left-lift-factor-proofᵀ
    liftρ
    (right-only-prefix-right
      {β = β} {B = B} {hB = hB} prefix)
    with right-only-store-prefix-left-lift-factor-proofᵀ
      liftρ prefix
right-only-store-prefix-left-lift-factor-proofᵀ
    liftρ
    (right-only-prefix-right
      {β = β} {B = B} {hB = hB} prefix)
    | ρ⁺ , prefix⁺ , lift⁺ =
  store-right β B hB ∷ ρ⁺ ,
  right-only-prefix-right prefix⁺ ,
  lift-left-store-right lift⁺
