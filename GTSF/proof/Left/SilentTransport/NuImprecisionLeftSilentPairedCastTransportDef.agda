module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedCastTransportDef where

-- File Charter:
--   * Defines transport of a paired cast through a completed left-silent
--     simulation result and an ambient store-imprecision prefix.
--   * Makes preservation of paired StoreCorresponds evidence in the final
--     world an explicit proof boundary.
--   * Contains no transport implementation or catch-up dispatcher.

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  )
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef using
  (WeakOneStepStoreLineage)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


LeftSilentPairedCastTransportᵀ : Set₁
LeftSilentPairedCastTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  WeakOneStepStoreLineage inner →
  WorldCoherent (resultStore inner) →
  PairedCast Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  PairedCast
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (resultStore inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner)
      (applyCoercion keep c′))
    {applyTys (sourceChanges inner) A}
    {applyTys (targetTailChanges inner) (applyTy keep A′)}
    {applyTys (sourceChanges inner) B}
    {applyTys (targetTailChanges inner) (applyTy keep B′)}
    (transportType inner p)
    (transportType inner q)
