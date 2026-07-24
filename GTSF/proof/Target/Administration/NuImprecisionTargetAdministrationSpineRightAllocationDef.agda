module
  proof.Target.Administration.NuImprecisionTargetAdministrationSpineRightAllocationDef
  where

-- File Charter:
--   * States hereditary target-administration spine transport through one
--     right-only runtime allocation.
--   * Shifts every pending outer coercion, lifts both precision indices on
--     the target, and uses the exact allocated relational store.
--   * Contains no implementation, simulation result, outcome carrier,
--     postulate, hole, permissive option, or compatibility wrapper.

open import Coercions using (Coercion; ⇑ᶜ)
open import Data.List using (List; map; _∷_)
open import Data.Nat using (suc; zero)
open import Imprecision using (ImpCtx; ⇑ᴿᵢ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (LiftRightStoreⁱ; StoreImp; store-right)
open import Types using (Ty; TyCtx; wf★; ★)
open import
  proof.EndpointMLB.Core.MaximalLowerBoundsWf
  using (⊑-target-lift-rightᵢ)
open import
  proof.Target.Administration.NuImprecisionTargetPendingCasts
  using (TargetAdministrationSpine)


TargetAdministrationSpineRightAllocationᵀ : Set
TargetAdministrationSpineRightAllocationᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρᴿ : StoreImp (⇑ᴿᵢ Φ) Δᴸ (suc Δᴿ)}
    {A B C : Ty} {cs : List Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
  LiftRightStoreⁱ (⇑ᴿᵢ Φ) ρ ρᴿ →
  TargetAdministrationSpine ρ A p q cs →
  TargetAdministrationSpine
    (store-right zero ★ wf★ ∷ ρᴿ)
    A
    (⊑-target-lift-rightᵢ p)
    (⊑-target-lift-rightᵢ q)
    (map ⇑ᶜ cs)
