module proof.NuCore.Misc.NuImprecisionCommonTargetExtensionCycleDef where

-- File Charter:
--   * Defines the type-only obstruction shared by paired-lambda target
--     closing: a paired lower cannot place a renamed copy of its middle
--     endpoint underneath one extra target universal.
--   * Keeps the span world and all three endpoint contexts exact.
--   * Contains no proof, conversion, store, term relation, simulation,
--     postulate, hole, permissive option, or broad proof import.

open import Data.Empty using (⊥)
open import Types using (Renameᵗ; Ty; TyCtx; `∀; renameᵗ)
open import proof.EndpointMLB.Simple.EndpointCanonicalMLBSimplePairedSpan using
  (PairedLower; SpanCtx)


CommonTargetExtensionCycleᵀ : Set
CommonTargetExtensionCycleᵀ =
  ∀ {Σ : SpanCtx} {Δᶜ Δᴸ Δᴿ : TyCtx}
    {C A : Ty} {ρ : Renameᵗ} →
  PairedLower Σ Δᶜ C A (`∀ (renameᵗ ρ A)) Δᴸ Δᴿ →
  ⊥
