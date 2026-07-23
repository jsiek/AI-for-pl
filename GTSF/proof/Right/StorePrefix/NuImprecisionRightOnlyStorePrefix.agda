module proof.Right.StorePrefix.NuImprecisionRightOnlyStorePrefix where

-- File Charter:
--   * Defines relational-store prefixes introduced exclusively by target-side
--     allocation.
--   * Records that every new entry is `store-right`, which is the information
--     lost by the generic `StoreImpPrefix` relation.
--   * Proves forgetting to the generic prefix relation.
--   * Contains no simulation result, term relation, postulate, hole,
--     permissive option, or broad simulation import.

open import Data.List using (_∷_)

open import NuTermImprecision using
  (StoreImp; store-right)
open import QuotientedTermImprecision using
  (StoreImpPrefix; prefix-reflⁱ; prefix-∷ⁱ)


data RightOnlyStoreImpPrefix
    {Φ Δᴸ Δᴿ} :
    StoreImp Φ Δᴸ Δᴿ →
    StoreImp Φ Δᴸ Δᴿ →
    Set where
  right-only-prefix-refl :
    ∀ {ρ} →
    RightOnlyStoreImpPrefix ρ ρ

  right-only-prefix-right :
    ∀ {ρ₀ ρ β B hB} →
    RightOnlyStoreImpPrefix ρ₀ ρ →
    RightOnlyStoreImpPrefix
      ρ₀ (store-right β B hB ∷ ρ)


right-only-store-prefix :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  RightOnlyStoreImpPrefix ρ₀ ρ⁺ →
  StoreImpPrefix ρ₀ ρ⁺
right-only-store-prefix right-only-prefix-refl =
  prefix-reflⁱ
right-only-store-prefix (right-only-prefix-right prefix) =
  prefix-∷ⁱ (right-only-store-prefix prefix)
