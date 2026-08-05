module Simulation.Indexed.InterpreterIndexedApplyValue where

-- File Charter:
--   * Exposes the positive-fuel dispatcher for exact `applyValue`
--     simulation.
--   * Separates ordinary closure and proxy observations from the quotient
--     observer callback.
--   * Makes all strictly smaller recursive calls explicit parameters.

open import Data.Nat using (suc)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (_⇒ᵛ_)
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
open import Types
import proof.InterpreterIndexedApplyValueProof as Proof

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-apply-value-positive :
  ∀ {left-index right-index} →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {N N′ : N.Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    IndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  IndexedCoercionSimulation left-index right-index →
  IndexedCoercionSimulation left-index (suc right-index) →
  IndexedCoercionSimulation (suc left-index) right-index →
  IndexedApplyValueSimulation left-index right-index →
  IndexedApplyValueSimulation left-index (suc right-index) →
  IndexedApplyValueSimulation (suc left-index) right-index →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    IndexedTerminalSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc left-index) (suc right-index)) →
  IndexedApplyValueSimulation
    (suc left-index) (suc right-index)
indexed-apply-value-positive =
  Proof.indexed-apply-value-positive
