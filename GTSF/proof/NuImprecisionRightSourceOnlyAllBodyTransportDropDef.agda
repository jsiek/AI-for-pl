module
  proof.NuImprecisionRightSourceOnlyAllBodyTransportDropDef
  where

-- File Charter:
--   * Defines removal of an unused source-only binder from target-only
--     transport below a matched universal binder.
--   * States the reusable commute/lift/transport/drop boundary independently
--     of any simulation result or catch-up carrier.
--   * Contains no implementation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import Data.Nat using (suc)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using (StoreChanges)
open import Types using (Ty; TyCtx)
open import proof.MaximalLowerBoundsWf using (∀ᵢᶜ; νᵢᶜ)
open import proof.ReductionProperties using (applyTysUnderTyBinders)


RightSourceOnlyAllBodyTransportDropᵀ : Set
RightSourceOnlyAllBodyTransportDropᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴿ : TyCtx}
    {χs : StoreChanges}
    (transport :
      ∀ {C D : Ty} →
      ∀ᵢᶜ (νᵢᶜ Φ)
        ∣ suc (suc Δᴸ) ⊢ C ⊑ D ⊣ suc Δᴿ →
      ∀ᵢᶜ (νᵢᶜ Ψ)
        ∣ suc (suc Δᴸ)
        ⊢ C ⊑ applyTysUnderTyBinders χs D
        ⊣ suc Θᴿ) →
  ∀ {C D : Ty} →
  ∀ᵢᶜ Φ ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ∀ᵢᶜ Ψ
    ∣ suc Δᴸ
    ⊢ C ⊑ applyTysUnderTyBinders χs D
    ⊣ suc Θᴿ
