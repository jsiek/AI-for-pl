module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportDef where

-- File Charter:
--   * Defines transport of the paired-widening constructor through a
--     completed left-silent simulation result and ambient store prefix.
--   * Isolates the constructor family that requires no StoreCorresponds or
--     final-world coherence reasoning.
--   * Contains no transport implementation or paired-conversion case.

open import Coercions using (Coercion; ModeEnv)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using
  (_∣_∣_⊢_∶_⊑_)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
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
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions)


LeftSilentPairedWideningTransportᵀ : Set₁
LeftSilentPairedWideningTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {μ μ′ : ModeEnv} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ₀) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ₀ ⊢ c ∶ A ⊑ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ₀) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c′ ∶ A′ ⊑ B′ →
  PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′ →
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
