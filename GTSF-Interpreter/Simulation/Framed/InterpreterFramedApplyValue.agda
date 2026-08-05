module Simulation.Framed.InterpreterFramedApplyValue where

-- File Charter:
--   * Exposes positive-fuel application simulation for exact framed values.
--   * Makes term, coercion, application, and quotient callbacks explicit.
--   * Delegates the exhaustive reduction-free dispatcher to `proof/`.

open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
import Data.Nat
open import Interpreter
open import Simulation.Framed.InterpreterFramedSimulationMotive
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Indexed.InterpreterIndexedSimulationMotive using
  (IndexedApplyValueSimulation)
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTypedValueNarrowing using (TypedValueNarrowing)
import NuTermImprecision as NTI
import NuTerms as N
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
import proof.InterpreterFramedApplyValueProof as Proof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

indexed-framed-apply-value-positive :
  ∀ {left-index right-index} →
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {γᵀ : NTI.CtxImp Φ Δᴸ Δᴿ}
      {N N′ : N.Term} {A B : Ty}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
    FramedIndexedInterpreterTermSimulation
      left-index right-index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  FramedIndexedCoercionSimulation left-index right-index →
  FramedIndexedCoercionSimulation left-index (Data.Nat.suc right-index) →
  FramedIndexedCoercionSimulation (Data.Nat.suc left-index) right-index →
  FramedIndexedApplyValueSimulation left-index right-index →
  FramedIndexedApplyValueSimulation
    left-index (Data.Nat.suc right-index) →
  FramedIndexedApplyValueSimulation
    (Data.Nat.suc left-index) right-index →
  IndexedApplyValueSimulation
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index) →
  (∀ {W W′ Φ Δᴸ Δᴿ}
      {ρ : NTI.StoreImp Φ Δᴸ Δᴿ}
      {θ θ′ A A′ B B′ V V′ U U′}
      {pA : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
      {pB : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
      {R : WorldRelation W W′} →
    AssumptionMembershipUnique Φ →
    (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
    TypedValueNarrowing
      ⟦ A ⇒ B ⟧[ θ ] ⟦ A′ ⇒ B′ ⟧[ θ′ ] R V V′ →
    FramedValueOrigin runtime
      (pA ImprecisionWf.↦ pB) V V′ →
    FramedValueNarrowing
      {A = A} {A′ = A′} {p = pA} runtime U U′ →
    IndexedTerminalSimulation
      (FramedValueResult ρ θ θ′ pB) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (Data.Nat.suc left-index)
      (Data.Nat.suc right-index)) →
  FramedIndexedApplyValueSimulation
    (Data.Nat.suc left-index)
    (Data.Nat.suc right-index)
indexed-framed-apply-value-positive =
  Proof.indexed-framed-apply-value-positive
