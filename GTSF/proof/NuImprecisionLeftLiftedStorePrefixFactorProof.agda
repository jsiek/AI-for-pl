module
  proof.NuImprecisionLeftLiftedStorePrefixFactorProof
  where

-- File Charter:
--   * Proves inverse source-only lifted-store prefix factorization by
--     exhaustive recursion on the lift and prefix derivations.
--   * Removes matching front entries from the lifted and base stores and
--     preserves the residual lift exactly.
--   * Contains no term relation, postulate, hole, catch-all, permissive
--     option, termination bypass, or broad simulation import.

open import Data.Product using (_,_)
open import NuTermImprecision using
  ( lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  )
open import QuotientedTermImprecision using
  (prefix-reflⁱ; prefix-∷ⁱ)
open import
  proof.NuImprecisionLeftLiftedStorePrefixFactorDef
  using (LeftLiftedStorePrefixFactorᵀ)


left-lifted-store-prefix-factor-proofᵀ :
  LeftLiftedStorePrefixFactorᵀ
left-lifted-store-prefix-factor-proofᵀ
    {ρ⁺ = ρ⁺} liftρ prefix-reflⁱ =
  ρ⁺ , prefix-reflⁱ , liftρ
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-∷ liftρ) (prefix-∷ⁱ prefix)
    with left-lifted-store-prefix-factor-proofᵀ liftρ prefix
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-∷ liftρ) (prefix-∷ⁱ prefix)
    | ρ₀ , prefix₀ , lift₀ =
  ρ₀ , prefix-∷ⁱ prefix₀ , lift₀
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-left liftρ) (prefix-∷ⁱ prefix)
    with left-lifted-store-prefix-factor-proofᵀ liftρ prefix
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-left liftρ) (prefix-∷ⁱ prefix)
    | ρ₀ , prefix₀ , lift₀ =
  ρ₀ , prefix-∷ⁱ prefix₀ , lift₀
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-right liftρ) (prefix-∷ⁱ prefix)
    with left-lifted-store-prefix-factor-proofᵀ liftρ prefix
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-right liftρ) (prefix-∷ⁱ prefix)
    | ρ₀ , prefix₀ , lift₀ =
  ρ₀ , prefix-∷ⁱ prefix₀ , lift₀
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-link liftρ) (prefix-∷ⁱ prefix)
    with left-lifted-store-prefix-factor-proofᵀ liftρ prefix
left-lifted-store-prefix-factor-proofᵀ
    (lift-left-store-link liftρ) (prefix-∷ⁱ prefix)
    | ρ₀ , prefix₀ , lift₀ =
  ρ₀ , prefix-∷ⁱ prefix₀ , lift₀
