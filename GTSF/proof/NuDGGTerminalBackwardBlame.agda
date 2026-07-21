{-# OPTIONS --allow-unsolved-metas #-}

module proof.NuDGGTerminalBackwardBlame where

-- File Charter:
--   * Owns the exact backward target-blame terminal theorem required by the
--     closed Nu DGG spine.
--   * The statement is frozen and checked; its proof will combine target-step
--     simulation, target-blame catch-up, alignment, and trace induction.

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
open import proof.NuDGGClosedWorld using (empty-store-wf)


backward-target-blame-generalᵀ :
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
backward-target-blame-generalᵀ = {!!}


backward-target-blameᵀ :
  ∀ {N N′ A B} {p : [] ∣ 0 ⊢ A ⊑ B ⊣ 0} →
  RuntimeOK N →
  RuntimeOK N′ →
  [] ∣ 0 ∣ 0 ∣ [] ∣ [] ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p →
  ∀ χs′ →
  N′ —↠[ χs′ ] blame →
  ∃[ χs ] (N —↠[ χs ] blame)
backward-target-blameᵀ okN okN′ N⊑N′ =
  backward-target-blame-generalᵀ
    empty-store-wf empty-store-wf okN okN′ N⊑N′
