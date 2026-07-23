module
  proof.Right.Core.NuImprecisionRightSilentQuotientWideningPairTransportDef
  where

-- File Charter:
--   * Defines transport of a quotient widening pair through a completed
--     right-silent simulation result and an ambient store-imprecision prefix.
--   * Keeps both source-silence facts as direct premises.
--   * Contains no implementation, auxiliary carrier, postulate, or hole.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion)
open import Data.List using ([])
open import ImprecisionWf using (ImpCtx)
open import NuReduction using
  (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp)
open import NuTerms using (Term)
open import QuotientedTermImprecision using
  (QuotientWideningPair; StoreImpPrefix)
open import Types using (Ty; TyCtx)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( WeakOneStepResult
  ; resultLeftCtx
  ; resultRightCtx
  ; resultStore
  ; sourceChanges
  ; sourceResult
  ; targetTailChanges
  )
open import proof.Core.Properties.ReductionProperties using (applyCoercions)


RightSilentQuotientWideningPairTransportᵀ : Set₁
RightSilentQuotientWideningPairTransportᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {M M′ : Term} {C C′ D D′ A A′ : Ty}
    {u u′ : Coercion}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  (inner : WeakOneStepResult ρ⁺ M M′ C C′ keep) →
  sourceChanges inner ≡ [] →
  sourceResult inner ≡ M →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPair
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (resultStore inner)
    (applyCoercions (sourceChanges inner) u)
    (applyCoercions (targetTailChanges inner)
      (applyCoercion keep u′))
    (applyTys (sourceChanges inner) D)
    (applyTys (targetTailChanges inner) (applyTy keep D′))
    (applyTys (sourceChanges inner) A)
    (applyTys (targetTailChanges inner) (applyTy keep A′))
