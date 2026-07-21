module proof.NuImprecisionRightStorePrefixFactorProof where

-- File Charter:
--   * Proves the strict `RightStorePrefixFactorᵀ` contract.
--   * Factors a right store lift through an ambient relational-store prefix by
--     exhaustive structural recursion on `StoreImpPrefix` and
--     `LiftRightStoreⁱ`.
--   * Depends only on the theorem definition and the store-lift/prefix
--     constructor owners; contains no simulation import.

open import Data.Product using (_,_)
open import NuTermImprecision using
  ( LiftRightStoreⁱ
  ; lift-right-store-[]
  ; lift-right-store-left
  ; lift-right-store-link
  ; lift-right-store-right
  ; lift-right-store-∷
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import proof.NuImprecisionRightStorePrefixFactorDef using
  (RightStorePrefixFactorᵀ)


right-store-prefix-factor-proofᵀ : RightStorePrefixFactorᵀ
right-store-prefix-factor-proofᵀ {ρ⁺ᴿ = ρᴿ}
    prefix-reflⁱ lift-right-store-[] =
  ρᴿ , lift-right-store-[] , prefix-reflⁱ
right-store-prefix-factor-proofᵀ {ρ⁺ᴿ = ρᴿ}
    prefix-reflⁱ (lift-right-store-∷ liftρ) =
  ρᴿ , lift-right-store-∷ liftρ , prefix-reflⁱ
right-store-prefix-factor-proofᵀ {ρ⁺ᴿ = ρᴿ}
    prefix-reflⁱ (lift-right-store-left liftρ) =
  ρᴿ , lift-right-store-left liftρ , prefix-reflⁱ
right-store-prefix-factor-proofᵀ {ρ⁺ᴿ = ρᴿ}
    prefix-reflⁱ (lift-right-store-right liftρ) =
  ρᴿ , lift-right-store-right liftρ , prefix-reflⁱ
right-store-prefix-factor-proofᵀ {ρ⁺ᴿ = ρᴿ}
    prefix-reflⁱ (lift-right-store-link liftρ) =
  ρᴿ , lift-right-store-link liftρ , prefix-reflⁱ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-∷ liftρ)
    with right-store-prefix-factor-proofᵀ prefix liftρ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-∷ liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-left liftρ)
    with right-store-prefix-factor-proofᵀ prefix liftρ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-left liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-right liftρ)
    with right-store-prefix-factor-proofᵀ prefix liftρ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-right liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-link liftρ)
    with right-store-prefix-factor-proofᵀ prefix liftρ
right-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-right-store-link liftρ)
    | ρ₀ᴿ , lift₀ , prefixᴿ =
  ρ₀ᴿ , lift₀ , prefix-∷ⁱ prefixᴿ
