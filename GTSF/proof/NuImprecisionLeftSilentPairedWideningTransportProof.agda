module proof.NuImprecisionLeftSilentPairedWideningTransportProof where

-- File Charter:
--   * Implements left-silent transport for paired-widening casts.
--   * Reuses quotient-widening transport and converts the resulting
--     quotient-cast-widening evidence back to paired-widening.
--   * Exports only the frozen paired-widening transport proof.

open import Agda.Builtin.Equality using (refl)

open import Coercions using (id-only≤tag-or-idᵈ)
open import NarrowWiden using (widen-mode-relax)
open import NuTermImprecision using (seal★-tag-or-id)
open import QuotientedTermImprecision using
  ( paired-widening
  ; quotient-id-widening
  ; quotient-cast-widening
  )
open import TermTyping using (cast-tag-or-id)
open import proof.NuImprecisionCatchupQuotientSupport using
  (weak-one-step-transport-quotient-widening-pairᵀ)
open import
  proof.NuImprecisionLeftSilentPairedWideningTransportDef using
  (LeftSilentPairedWideningTransportᵀ)
open import proof.NuImprecisionSimulationResultDef using
  (left-silent-invariant)


left-silent-paired-widening-transport-proofᵀ :
  LeftSilentPairedWideningTransportᵀ
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑
    with weak-one-step-transport-quotient-widening-pairᵀ
      prefix inner (left-silent-invariant refl refl)
      (quotient-cast-widening
        mode seal★ c⊑ mode′ seal★′ c′⊑)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑
    | quotient-id-widening transported-c⊑ transported-c′⊑ =
  paired-widening
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c⊑)
    cast-tag-or-id seal★-tag-or-id
    (widen-mode-relax id-only≤tag-or-idᵈ transported-c′⊑)
left-silent-paired-widening-transport-proofᵀ
    prefix inner (left-silent-invariant refl refl)
    mode seal★ c⊑ mode′ seal★′ c′⊑
    | quotient-cast-widening
        transported-mode transported-seal★ transported-c⊑
        transported-mode′ transported-seal★′ transported-c′⊑ =
  paired-widening
    transported-mode transported-seal★ transported-c⊑
    transported-mode′ transported-seal★′ transported-c′⊑
