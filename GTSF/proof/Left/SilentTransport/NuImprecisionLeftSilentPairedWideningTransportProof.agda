module proof.Left.SilentTransport.NuImprecisionLeftSilentPairedWideningTransportProof where

-- File Charter:
--   * Implements left-silent transport for paired-widening casts.
--   * Reuses quotient-widening transport and converts the resulting
--     quotient-cast-widening evidence back to paired-widening.
--   * Exports only the frozen paired-widening transport proof.

open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_,_)

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
  ; WeakOneStepTypeCoherence
  ; left-silent-invariant
  ; resultCtx
  ; resultLeftCtx
  ; resultRightCtx
  ; sourceChanges
  ; targetTailChanges
  ; transportShapeCoherent
  ; transportType
  )
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  ( cast-shape-applyCoercions
  ; imprecision-composition-shape-transport
  )
open import proof.Core.Properties.ReductionProperties using
  (applyCoercions; applyCoercions-preserves-Inert)
open import Types using (Ty; TyCtx)


left-silent-paired-widening-compatible-transportᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {M M′ : Term} {C C′ A A′ B B′ : Ty}
    {c c′ : Coercion} {p q s s′} →
  (inner : WeakOneStepResult ρ M M′ C C′ keep) →
  LeftSilentInvariant inner →
  (coherent : WeakOneStepTypeCoherence inner) →
  PairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′} p q s s′ →
  PairedWideningCompatible
    (resultCtx inner)
    (resultLeftCtx inner)
    (resultRightCtx inner)
    (applyCoercions (sourceChanges inner) c)
    (applyCoercions (targetTailChanges inner) (applyCoercion keep c′))
    (transportType inner p)
    (transportType inner q)
    s s′
left-silent-paired-widening-compatible-transportᵀ
    inner silent coherent (compatible-source-inert inert) =
  compatible-source-inert
    (applyCoercions-preserves-Inert (sourceChanges inner) inert)
left-silent-paired-widening-compatible-transportᵀ
    inner (left-silent-invariant refl refl) coherent
    (compatible-target-inert-bridge bridge-evidence) =
  compatible-target-inert-bridge λ target-inert →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence target-inert
    in
      transportType inner bridge ,
      imprecision-composition-shape-transport
        refl (transportShapeCoherent coherent bridge)
        (transportShapeCoherent coherent _) source-triangle ,
      imprecision-composition-shape-transport
        (transportShapeCoherent coherent bridge) refl
        (transportShapeCoherent coherent _) target-triangle


left-silent-paired-widening-transport-proofᵀ :
  LeftSilentPairedWideningTransportᵀ
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    coherent
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    left-square right-square compat
    with weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner (left-silent-invariant refl refl)
      (quotient-cast-widening
        mode seal★ c⊑ mode′ seal★′ c′⊑)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    coherent
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    left-square right-square compat
    | quotient-id-widening transported-c⊑ transported-c′⊑ =
  paired-widening
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c⊑)
    (cast-shape-applyCoercions
      (sourceChanges inner) c-shape)
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c′⊑)
    (cast-shape-applyCoercions
      (targetTailChanges inner) c′-shape)
    (imprecision-composition-shape-transport
      refl (transportShapeCoherent coherent _) refl left-square)
    (imprecision-composition-shape-transport
      (transportShapeCoherent coherent _) refl refl right-square)
    (left-silent-paired-widening-compatible-transportᵀ
      inner (left-silent-invariant refl refl) coherent compat)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    coherent
    mode seal★ c⊑ c-shape
    mode′ seal★′ c′⊑ c′-shape
    left-square right-square compat
    | quotient-cast-widening
        transported-mode transported-seal★ transported-c⊑
        transported-mode′ transported-seal★′ transported-c′⊑ =
  paired-widening
    transported-mode transported-seal★ transported-c⊑
    (cast-shape-applyCoercions
      (sourceChanges inner) c-shape)
    transported-mode′ transported-seal★′ transported-c′⊑
    (cast-shape-applyCoercions
      (targetTailChanges inner) c′-shape)
    (imprecision-composition-shape-transport
      refl (transportShapeCoherent coherent _) refl left-square)
    (imprecision-composition-shape-transport
      (transportShapeCoherent coherent _) refl refl right-square)
    (left-silent-paired-widening-compatible-transportᵀ
      inner (left-silent-invariant refl refl) coherent compat)
