module Narrowing.InterpreterOperationalValueNarrowingProperties where

-- File Charter:
--   * Public weakening interface for exact operational value narrowing.
--   * States value and captured-environment transport explicitly.
--   * Delegates the structural proof to a reduction-free proof module.

open import Interpreter
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using
  (SemanticType; WorldTyping)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterOperationalValueNarrowingProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

operational-value-narrowing-weaken :
  ∀ {W W′ U U′ A B V V′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  WorldTyping U →
  WorldTyping U′ →
  OperationalValueNarrowing A B R V V′ →
  OperationalValueNarrowing A B S V V′
operational-value-narrowing-weaken =
  Proof.operational-value-narrowing-weaken

operational-value-origin-weaken :
  ∀ {W W′ U U′ A B V V′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  WorldTyping U →
  WorldTyping U′ →
  OperationalValueOrigin A B R V V′ →
  OperationalValueOrigin A B S V V′
operational-value-origin-weaken =
  Proof.operational-value-origin-weaken

operational-environment-narrowing-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ θ θ′ γᵀ γ γ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  WorldTyping U →
  WorldTyping U′ →
  OperationalEnvironmentNarrowing
    θ θ′ R {Φ} {Δᴸ} {Δᴿ} γᵀ γ γ′ →
  OperationalEnvironmentNarrowing
    θ θ′ S γᵀ γ γ′
operational-environment-narrowing-weaken =
  Proof.operational-environment-narrowing-weaken
