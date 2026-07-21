module proof.NuImprecisionPairedStorePrefixFactorProof where

-- File Charter:
--   * Proves the strict `PairedStorePrefixFactorᵀ` contract.
--   * Factors a matched store lift through an ambient relational-store prefix
--     by exhaustive structural recursion on `StoreImpPrefix` and `LiftStoreⁱ`.
--   * Depends only on the theorem definition and the store-lift/prefix
--     constructor owners; contains no simulation import.

open import Data.Product using (_,_)
open import NuTermImprecision using
  ( LiftStoreⁱ
  ; lift-store-[]
  ; lift-store-left
  ; lift-store-link
  ; lift-store-right
  ; lift-store-∷
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import proof.NuImprecisionPairedStorePrefixFactorDef using
  (PairedStorePrefixFactorᵀ)


paired-store-prefix-factor-proofᵀ : PairedStorePrefixFactorᵀ
paired-store-prefix-factor-proofᵀ {ρ⁺∀ = ρ∀}
    prefix-reflⁱ lift-store-[] =
  ρ∀ , lift-store-[] , prefix-reflⁱ
paired-store-prefix-factor-proofᵀ {ρ⁺∀ = ρ∀}
    prefix-reflⁱ (lift-store-∷ liftρ) =
  ρ∀ , lift-store-∷ liftρ , prefix-reflⁱ
paired-store-prefix-factor-proofᵀ {ρ⁺∀ = ρ∀}
    prefix-reflⁱ (lift-store-left liftρ) =
  ρ∀ , lift-store-left liftρ , prefix-reflⁱ
paired-store-prefix-factor-proofᵀ {ρ⁺∀ = ρ∀}
    prefix-reflⁱ (lift-store-right liftρ) =
  ρ∀ , lift-store-right liftρ , prefix-reflⁱ
paired-store-prefix-factor-proofᵀ {ρ⁺∀ = ρ∀}
    prefix-reflⁱ (lift-store-link liftρ) =
  ρ∀ , lift-store-link liftρ , prefix-reflⁱ
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-∷ liftρ)
    with paired-store-prefix-factor-proofᵀ prefix liftρ
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-∷ liftρ)
    | ρ₀∀ , lift₀ , prefix∀ =
  ρ₀∀ , lift₀ , prefix-∷ⁱ prefix∀
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-left liftρ)
    with paired-store-prefix-factor-proofᵀ prefix liftρ
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-left liftρ)
    | ρ₀∀ , lift₀ , prefix∀ =
  ρ₀∀ , lift₀ , prefix-∷ⁱ prefix∀
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-right liftρ)
    with paired-store-prefix-factor-proofᵀ prefix liftρ
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-right liftρ)
    | ρ₀∀ , lift₀ , prefix∀ =
  ρ₀∀ , lift₀ , prefix-∷ⁱ prefix∀
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-link liftρ)
    with paired-store-prefix-factor-proofᵀ prefix liftρ
paired-store-prefix-factor-proofᵀ
    (prefix-∷ⁱ prefix) (lift-store-link liftρ)
    | ρ₀∀ , lift₀ , prefix∀ =
  ρ₀∀ , lift₀ , prefix-∷ⁱ prefix∀
