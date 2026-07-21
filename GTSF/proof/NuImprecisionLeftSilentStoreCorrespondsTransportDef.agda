module proof.NuImprecisionLeftSilentStoreCorrespondsTransportDef where

-- File Charter:
--   * Defines structural transport of one stored or linked correspondence
--     through an ambient prefix and both sides of a weak simulation result.
--   * Exposes the relational-store information absent from projected store
--     equalities, especially preservation of store-link entries.
--   * Contains no paired-conversion or catch-up implementation.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc)
open import Data.Product using (∃-syntax)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  ( StoreChanges
  ; applyTys
  ; bind
  ; keep
  )
open import NuTermImprecision using
  (StoreCorresponds; StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (StoreImpPrefix)
open import Types using (Ty; TyCtx; TyVar)
open import proof.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  )


applyTyVars : StoreChanges → TyVar → TyVar
applyTyVars [] α = α
applyTyVars (keep ∷ χs) α = applyTyVars χs α
applyTyVars (bind A ∷ χs) α = applyTyVars χs (suc α)


LeftSilentStoreCorrespondsTransportᵀ : Set₁
LeftSilentStoreCorrespondsTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ : Ty}
    {α β : TyVar} {X X′ : Ty}
    {pX : Φ ∣ Δᴸ ⊢ X ⊑ X′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  StoreCorresponds ρ₀ α X β X′ pX →
  ∃[ pX′ ]
    StoreCorresponds
      (resultStore inner)
      (applyTyVars (sourceChanges inner) α)
      (applyTys (sourceChanges inner) X)
      (applyTyVars (targetTailChanges inner) β)
      (applyTys (targetTailChanges inner) X′)
      pX′
