module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyTransportDropDef
  where

-- File Charter:
--   * Defines removal of an unused source-only binder from a target-only
--     type-transport function.
--   * States the reusable lift/transport/drop boundary independently of any
--     simulation result or catch-up carrier.
--   * Contains no implementation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _∣_⊢_⊑_⊣_; ⇑ᴸᵢ)
open import NuReduction using (StoreChanges; applyTys)
open import Types using (Ty; TyCtx; ⇑ᵗ)


RightSourceOnlyTransportDropᵀ : Set
RightSourceOnlyTransportDropᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴿ : TyCtx}
    {χs : StoreChanges}
    (transport :
      ∀ {C D : Ty} →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Ψ)
        ∣ suc Δᴸ ⊢ C ⊑ applyTys χs D ⊣ Θᴿ) →
  ∀ {C D : Ty} →
  Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ Δᴿ →
  Ψ ∣ Δᴸ ⊢ C ⊑ applyTys χs D ⊣ Θᴿ
