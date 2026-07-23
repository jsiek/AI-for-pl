module
  proof.Right.SourceOnly.NuImprecisionRightSourceOnlyRightBodyTransportDropDef
  where

-- File Charter:
--   * Defines removal of an unused source-only binder from target-only
--     transport below a target universal binder.
--   * States the reusable commute/lift/transport/drop boundary independently
--     of any simulation result or catch-up carrier.
--   * Contains no implementation, postulate, hole, permissive option,
--     termination bypass, or broad simulation import.

open import Data.Nat using (suc)

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_; ⇑ᴿᵢ)
open import NuReduction using (StoreChanges)
open import Types using (Ty; TyCtx)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (νᵢᶜ)
open import proof.Core.Properties.ReductionProperties using (applyTysUnderTyBinders)


RightSourceOnlyRightBodyTransportDropᵀ : Set
RightSourceOnlyRightBodyTransportDropᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴿ : TyCtx}
    {χs : StoreChanges}
    (transport :
      ∀ {C D : Ty} →
      ⇑ᴿᵢ (νᵢᶜ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
      ⇑ᴿᵢ (νᵢᶜ Ψ)
        ∣ suc Δᴸ
        ⊢ C ⊑ applyTysUnderTyBinders χs D
        ⊣ suc Θᴿ) →
  ∀ {C D : Ty} →
  ⇑ᴿᵢ Φ ∣ Δᴸ ⊢ C ⊑ D ⊣ suc Δᴿ →
  ⇑ᴿᵢ Ψ
    ∣ Δᴸ
    ⊢ C ⊑ applyTysUnderTyBinders χs D
    ⊣ suc Θᴿ
