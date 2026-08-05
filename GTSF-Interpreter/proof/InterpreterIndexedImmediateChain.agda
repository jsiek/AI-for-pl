module proof.InterpreterIndexedImmediateChain where

-- File Charter:
--   * Removes a computation chain whose head is an immediate return.
--   * States both the unguarded chain and guarded sequence equations.
--   * Uses only the continuation's explicit zero-index timeout equation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (sym)

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult

immediate-chain-computation-eq :
  ∀ {W V}
    {continuation : World → Value → Computation} →
  continuation W V zero ≡ timed W →
  ∀ n →
  chain (immediateReturn W V) continuation n ≡
    continuation W V n
immediate-chain-computation-eq continuation-zero zero =
  sym continuation-zero
immediate-chain-computation-eq continuation-zero (suc n) =
  refl

immediate-sequence-computation-eq :
  ∀ {W V}
    {continuation : World → Value → Computation} →
  continuation W V zero ≡ timed W →
  ∀ n →
  sequence W (immediateReturn W V) continuation n ≡
    guard W (continuation W V) n
immediate-sequence-computation-eq continuation-zero zero =
  refl
immediate-sequence-computation-eq continuation-zero (suc n) =
  immediate-chain-computation-eq continuation-zero n
