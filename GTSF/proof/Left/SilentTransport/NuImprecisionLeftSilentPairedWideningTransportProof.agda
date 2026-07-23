module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportProof where

-- File Charter:
--   * Implements left-silent transport for paired-widening casts.
--   * Reuses quotient-widening transport and converts the resulting
--     quotient-cast-widening evidence back to paired-widening.
--   * Exports only the frozen paired-widening transport proof.

open import Agda.Builtin.Equality using (refl)

open import Coercions using (Coercion; id-only≤tag-or-idᵈ)
open import ImprecisionWf using (ImpCtx)
open import NarrowWiden using (widen-mode-relax)
open import NuReduction using (applyCoercion; applyTy; applyTys; keep)
open import NuTermImprecision using (StoreImp; seal★-tag-or-id)
open import NuTerms using (Term)
open import PairedWideningCompatibility using
  ( PairedWideningCompatible
  ; compatible-source-inert
  ; compatible-target-inert-bridge
  )
open import QuotientedTermImprecision using
  ( paired-widening
  ; quotient-id-widening
  ; quotient-cast-widening
  )
open import TermTyping using (cast-tag-or-id)
open import proof.Quotient.NuImprecisionQuotientWideningTransport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import
  proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)
open import proof.Catchup.Simulation.NuImprecisionSimulationResultDef using
  ( LeftSilentInvariant
  ; WeakOneStepResult
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; targetTailChanges
  ; transportType
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert)
open import Types using (Ty; TyCtx)


left-silent-paired-widening-compatible-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ B A′ : Ty}
    {c c′ : Coercion} →
  (inner : WeakOneStepResult ρ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′ →
  PairedWideningCompatible
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner) (applyCoercion keep c′))
    (applyTys (sourceChanges inner) B)
    (applyTys (targetTailChanges inner) (applyTy keep A′))
left-silent-paired-widening-compatible-transportᵀ
    inner silent (compatible-source-inert inert) =
  compatible-source-inert
    (applyCoercions-preserves-Inert (sourceChanges inner) inert)
left-silent-paired-widening-compatible-transportᵀ
    inner (left-silent-invariant refl refl)
    (compatible-target-inert-bridge bridge) =
  compatible-target-inert-bridge
    (λ target-inert → transportType inner (bridge target-inert))


left-silent-paired-widening-transport-proofᵀ :
  LeftSilentPairedWideningTransportᵀ
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑ compat
    with weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner (left-silent-invariant refl refl)
      (quotient-cast-widening
        mode seal★ c⊑ mode′ seal★′ c′⊑)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑ compat
    | quotient-id-widening transported-c⊑ transported-c′⊑ =
  paired-widening
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c⊑)
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c′⊑)
    (left-silent-paired-widening-compatible-transportᵀ
      inner (left-silent-invariant refl refl) compat)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑ compat
    | quotient-cast-widening
        transported-mode transported-seal★ transported-c⊑
        transported-mode′ transported-seal★′ transported-c′⊑ =
  paired-widening
    transported-mode transported-seal★ transported-c⊑
    transported-mode′ transported-seal★′ transported-c′⊑
    (left-silent-paired-widening-compatible-transportᵀ
      inner (left-silent-invariant refl refl) compat)
