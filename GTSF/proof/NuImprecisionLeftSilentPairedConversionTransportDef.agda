module proof.NuImprecisionLeftSilentPairedConversionTransportDef where

-- File Charter:
--   * Defines transport of paired reveal/conceal conversions through a
--     completed left-silent simulation result and ambient store prefix.
--   * Makes reconstruction of the final paired StoreCorresponds witness from
--     world coherence an explicit constructor-family boundary.
--   * Contains no transport implementation or paired-widening case.

open import Coercions using (Coercion)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (PairedConversion; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionSimulationResultDef using
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
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.ReductionProperties using
  (applyCoercions)


LeftSilentPairedConversionTransportᵀ : Set₁
LeftSilentPairedConversionTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  WorldCoherent (resultStore inner) →
  PairedConversion Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  PairedConversion
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
