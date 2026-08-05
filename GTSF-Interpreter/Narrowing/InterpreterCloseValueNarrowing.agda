module Narrowing.InterpreterCloseValueNarrowing where

-- File Charter:
--   * Public fundamental theorem for closing related syntactic values.
--   * States the direct semantic-value result without observation wrappers.
--   * Delegates its reduction-free proof to a private module.

open import Data.Maybe using (just)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Interpreter
import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore using
  (EnvironmentTyping)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
import NuTermImprecision as NTI
import NuTerms as N
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Types
import proof.InterpreterCloseValueNarrowingProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

closeValue-preserves-narrowing :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p}
    {R : WorldRelation W W′}
    {γ γ′ θ θ′ U U′} →
  OpenInterpreterTermNarrowing
    R Φ Δᴸ Δᴿ ρ γᵀ M M′ A B p →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  EnvironmentTyping W θ γ (NTI.leftCtxⁱ γᵀ) →
  EnvironmentTyping W′ θ′ γ′ (NTI.rightCtxⁱ γᵀ) →
  TypeEnvironmentRealization R Φ θ θ′ →
  EnvironmentNarrowing R γ γ′ →
  nextAbstractIndex θ′ ≤ nextAbstractIndex θ →
  (vM : N.Value M) →
  (vM′ : N.Value M′) →
  closeValue vM γ θ ≡ just U →
  closeValue vM′ γ′ θ′ ≡ just U′ →
  ValueNarrowing R U U′
closeValue-preserves-narrowing =
  Proof.closeValue-preserves-narrowing
