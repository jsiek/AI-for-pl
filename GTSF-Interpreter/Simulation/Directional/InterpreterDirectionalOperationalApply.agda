module Simulation.Directional.InterpreterDirectionalOperationalApply where

-- File Charter:
--   * Exposes the positive-fuel directional dispatcher for operational
--     `applyValue`.
--   * Makes predecessor, target-only, and quotient-origin callbacks explicit.
--   * Contains no recursion, reduction, or catch-up theorem.

open import Data.Nat using (suc)
open import Data.Product using (_×_)

open import Interpreter using (applyValue)
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore using (_⇒ᵛ_)
import Narrowing.InterpreterTermNarrowing as ITN
import proof.InterpreterDirectionalOperationalApplyProof as Proof


directional-operational-apply-forward-positive :
  ∀ {index} →
  (∀ {Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p} →
    FramedDirectionalInterpreterTermSimulation
      forward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  DirectionalCoercionSimulation forward-direction index →
  DirectionalApplyValueSimulation forward-direction index →
  DirectionalCoercionSimulation forward-direction (suc index) →
  DirectionalApplyValueSimulation forward-direction (suc index) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : ITN.RelatedWorlds.WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    NameInstantiatedOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    ForwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : ITN.RelatedWorlds.WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    ForwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U)
      (applyValue W′ V′ U′)
      (suc index)) →
  DirectionalApplyValueSimulation forward-direction (suc index)
directional-operational-apply-forward-positive =
  Proof.directional-operational-apply-forward-positive


directional-operational-apply-backward-positive :
  ∀ {index} →
  (∀ {Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p} →
    FramedDirectionalInterpreterTermSimulation
      backward-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p
    ×
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction index Φ Δᴸ Δᴿ ρ γᵀ N N′ A B p) →
  (DirectionalCoercionSimulation backward-direction index
   × DirectionalCoercionSimulation
       target-blame-direction index) →
  (DirectionalApplyValueSimulation backward-direction index
   × DirectionalApplyValueSimulation
       target-blame-direction index) →
  (DirectionalCoercionSimulation
       backward-direction (suc index)
   × DirectionalCoercionSimulation
       target-blame-direction (suc index)) →
  (DirectionalApplyValueSimulation
       backward-direction (suc index)
   × DirectionalApplyValueSimulation
       target-blame-direction (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : ITN.RelatedWorlds.WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    NameInstantiatedOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U) (applyValue W′ V′ U′)
      (suc index)) →
  (∀ {W W′ A A′ B B′ V V′ U U′}
      {R : ITN.RelatedWorlds.WorldRelation W W′} →
    (value :
      OperationalValueNarrowing
        (A ⇒ᵛ B) (A′ ⇒ᵛ B′) R V V′) →
    QuotientOperationalOrigin (operational-origin value) →
    OperationalValueNarrowing A A′ R U U′ →
    BackwardReturnSimulation
      (OperationalValueResult B B′) R
      (applyValue W V U)
      (applyValue W′ V′ U′)
      (suc index)
    ×
    TargetBlameSimulation R
      (applyValue W V U)
      (applyValue W′ V′ U′)
      (suc index)) →
  (DirectionalApplyValueSimulation
      backward-direction (suc index)
   ×
   DirectionalApplyValueSimulation
      target-blame-direction (suc index))
directional-operational-apply-backward-positive =
  Proof.directional-operational-apply-backward-positive
