module proof.NuImprecisionStorePrefix where

-- File Charter:
--   * Defines the structural action of store-imprecision prefixes on the
--     projected source and target stores.
--   * Proves transitivity of store-imprecision prefixes.
--   * Depends only on the store-imprecision and prefix definitions.

open import Data.List.Relation.Unary.Any using (there)

open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  ; store-matched
  ; store-left
  ; store-right
  ; store-link
  )
open import QuotientedTermImprecision using
  ( StoreImpPrefix
  ; prefix-reflⁱ
  ; prefix-∷ⁱ
  )
open import Store using (StoreIncl)

leftStoreⁱ-prefix-inclusion :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreIncl (leftStoreⁱ ρ₀) (leftStoreⁱ ρ⁺)
leftStoreⁱ-prefix-inclusion prefix-reflⁱ x∈ = x∈
leftStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) x∈ =
  there (leftStoreⁱ-prefix-inclusion prefix x∈)
leftStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) x∈ =
  there (leftStoreⁱ-prefix-inclusion prefix x∈)
leftStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) x∈ =
  leftStoreⁱ-prefix-inclusion prefix x∈
leftStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) x∈ =
  leftStoreⁱ-prefix-inclusion prefix x∈

rightStoreⁱ-prefix-inclusion :
  ∀ {Φ Δᴸ Δᴿ} {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  StoreIncl (rightStoreⁱ ρ₀) (rightStoreⁱ ρ⁺)
rightStoreⁱ-prefix-inclusion prefix-reflⁱ x∈ = x∈
rightStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-matched α A β B p} prefix) x∈ =
  there (rightStoreⁱ-prefix-inclusion prefix x∈)
rightStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-left α A hA} prefix) x∈ =
  rightStoreⁱ-prefix-inclusion prefix x∈
rightStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-right β B hB} prefix) x∈ =
  there (rightStoreⁱ-prefix-inclusion prefix x∈)
rightStoreⁱ-prefix-inclusion
    (prefix-∷ⁱ {entry = store-link α A β B p} prefix) x∈ =
  rightStoreⁱ-prefix-inclusion prefix x∈

store-imp-prefix-transⁱ :
  ∀ {Φ Δᴸ Δᴿ}
    {ρ₀ ρ₁ ρ₂ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ₂ →
  StoreImpPrefix ρ₀ ρ₂
store-imp-prefix-transⁱ prefix₀₁ prefix-reflⁱ = prefix₀₁
store-imp-prefix-transⁱ prefix₀₁ (prefix-∷ⁱ prefix₁₂) =
  prefix-∷ⁱ (store-imp-prefix-transⁱ prefix₀₁ prefix₁₂)
