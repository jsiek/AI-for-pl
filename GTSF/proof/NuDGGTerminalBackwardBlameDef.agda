module proof.NuDGGTerminalBackwardBlameDef where

-- File Charter:
--   * Defines the arbitrary-world backward target-blame terminal contract.
--   * Separates the reusable statement from the old permissive implementation
--     shell and the higher-order trace assembly.
--   * Contains no implementation, postulate, hole, permissive option, or
--     broad proof import.

open import Data.List using ([])
open import Data.Product using (∃-syntax)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuReduction using (_—↠[_]_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; leftStoreⁱ
  ; rightStoreⁱ
  )
open import NuTerms using (RuntimeOK; blame)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)


BackwardTargetBlameᵀ : Set₁
BackwardTargetBlameᵀ =
  ∀ {Φ Δᴸ Δᴿ M M′ A B}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  StoreWf Δᴿ (rightStoreⁱ ρ) →
  RuntimeOK M →
  RuntimeOK M′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ M ⊑ M′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  M′ —↠[ χs′ ] blame →
  ∃[ χs ] (M —↠[ χs ] blame)
