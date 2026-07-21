module PairedWideningCompatibility where

-- File Charter:
--   * Defines compatibility between paired source and target widenings.
--   * Keeps inert source casts and requires a source-output/target-input
--     bridge whenever an active source is paired with an inert target.
--   * Contains no cast typing, term imprecision, or simulation proof.

open import Coercions using (Coercion; Inert)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using (Ty; TyCtx)


data PairedWideningCompatible
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (c c′ : Coercion) (B A′ : Ty) : Set where
  compatible-source-inert :
    Inert c →
    PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′

  compatible-target-inert-bridge :
    (Inert c′ → Φ ∣ Δᴸ ⊢ B ⊑ A′ ⊣ Δᴿ) →
    PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′
