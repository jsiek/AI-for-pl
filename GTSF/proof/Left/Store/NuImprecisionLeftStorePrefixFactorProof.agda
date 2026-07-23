module proof.Left.Store.NuImprecisionLeftStorePrefixFactorProof where

-- File Charter:
--   * Proves the strict `LeftStorePrefixFactorᵀ` contract.
--   * Factors a left store lift through a relational-store prefix by
--     exhaustive structural recursion on the prefix and lift derivations.
--   * Contains no simulation import, postulate, hole, catch-all, or
--     permissive option.

open import Data.Product using (_,_)

open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; lift-left-store-[]
  ; lift-left-store-left
  ; lift-left-store-link
  ; lift-left-store-right
  ; lift-left-store-∷
  )
open import QuotientedTermImprecision using
  (prefix-reflⁱ; prefix-∷ⁱ)
open import proof.Left.Store.NuImprecisionLeftStorePrefixFactorDef using
  (LeftStorePrefixFactorᵀ)


left-store-prefix-factor-proofᵀ : LeftStorePrefixFactorᵀ
left-store-prefix-factor-proofᵀ {ρ⁺ᴸ = ρᴸ}
    prefix-reflⁱ lift-left-store-[] =
  ρᴸ , lift-left-store-[] , prefix-reflⁱ
left-store-prefix-factor-proofᵀ {ρ⁺ᴸ = ρᴸ}
    prefix-reflⁱ (lift-left-store-∷ liftρ) =
  ρᴸ , lift-left-store-∷ liftρ , prefix-reflⁱ
left-store-prefix-factor-proofᵀ {ρ⁺ᴸ = ρᴸ}
    prefix-reflⁱ (lift-left-store-left liftρ) =
  ρᴸ , lift-left-store-left liftρ , prefix-reflⁱ
left-store-prefix-factor-proofᵀ {ρ⁺ᴸ = ρᴸ}
    prefix-reflⁱ (lift-left-store-right liftρ) =
  ρᴸ , lift-left-store-right liftρ , prefix-reflⁱ
left-store-prefix-factor-proofᵀ {ρ⁺ᴸ = ρᴸ}
    prefix-reflⁱ (lift-left-store-link liftρ) =
  ρᴸ , lift-left-store-link liftρ , prefix-reflⁱ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-∷ liftρ)
    with left-store-prefix-factor-proofᵀ prefix liftρ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-∷ liftρ)
    | ρ₀ᴸ , lift₀ , prefixᴸ =
  ρ₀ᴸ , lift₀ , prefix-∷ⁱ prefixᴸ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-left liftρ)
    with left-store-prefix-factor-proofᵀ prefix liftρ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-left liftρ)
    | ρ₀ᴸ , lift₀ , prefixᴸ =
  ρ₀ᴸ , lift₀ , prefix-∷ⁱ prefixᴸ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-right liftρ)
    with left-store-prefix-factor-proofᵀ prefix liftρ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-right liftρ)
    | ρ₀ᴸ , lift₀ , prefixᴸ =
  ρ₀ᴸ , lift₀ , prefix-∷ⁱ prefixᴸ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-link liftρ)
    with left-store-prefix-factor-proofᵀ prefix liftρ
left-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-left-store-link liftρ)
    | ρ₀ᴸ , lift₀ , prefixᴸ =
  ρ₀ᴸ , lift₀ , prefix-∷ⁱ prefixᴸ
