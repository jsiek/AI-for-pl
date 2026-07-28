module proof.Right.Core.NuImprecisionPairedCastTransportDef where

-- File Charter:
--   * Defines paired-cast transport through an arbitrary completed weak
--     one-step result, including its leading target store change.
--   * Retains the complete source and target change lists, exact transported
--     QTI indices, relational-store lineage, and final-world coherence.
--   * Contains no silence hypothesis, implementation, dispatcher, postulate,
--     hole, permissive option, or theorem-fragment alias.

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (StoreChange; applyCoercion; applyTy; applyTys)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  )
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import
  proof.Catchup.Simulation.NuImprecisionSimulationResultDef
  using
  ( WeakOneStepResult
  ; WeakOneStepTypeCoherence
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  )
open import
  proof.Store.Lineage.NuImprecisionWeakOneStepStoreLineageDef
  using (WeakOneStepStoreLineage)
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef
  using (WorldCoherent)
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


PairedCastTransportᵀ : Set₁
PairedCastTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {χ : StoreChange}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ χ) →
  WeakOneStepTypeCoherence inner →
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
      (applyCoercion χ c′))
    {applyTys (sourceChanges inner) A}
    {applyTys (targetTailChanges inner) (applyTy χ A′)}
    {applyTys (sourceChanges inner) B}
    {applyTys (targetTailChanges inner) (applyTy χ B′)}
    (transportType inner p)
    (transportType inner q)
