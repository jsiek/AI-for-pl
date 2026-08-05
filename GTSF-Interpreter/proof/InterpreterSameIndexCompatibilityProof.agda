module proof.InterpreterSameIndexCompatibilityProof where

-- File Charter:
--   * Proves same-index compatibility from asynchronous terminal simulation.
--   * Stabilizes the observed and simulated target returns to one fuel index.
--   * Contains no catch-up procedure, reduction, or DGG theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
import DGG.InterpreterJoined as JoinedDefinition
open import Core.InterpreterOutcome using (terminal-return)
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import proof.InterpreterSimulationHelpers using
  (terminal-stable-at-left-sum; terminal-stable-at-right-sum)

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module JoinedValues =
  JoinedDefinition.Joined interpreterNarrowingLeaves

same-index-returned-compatible :
  ∀ {W W′ U U′ V V′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left right →
  ∀ {n} →
  left n ≡ returned U V →
  right n ≡ returned U′ V′ →
  Σ[ S ∈ WorldRelation U U′ ]
    WorldExtension R S ×
    value-result S V V′
same-index-returned-compatible
    {U′ = U′} {V′ = V′} {right = right}
    simulation {n} left-eq right-eq
    with forward-return simulation left-eq
same-index-returned-compatible
    {U′ = U′} {V′ = V′} {right = right}
    simulation {n} left-eq right-eq
    | m , Z′ , Q′ , S , R≤S , simulated-eq , V~Q′
    with trans
      (sym
        (terminal-stable-at-left-sum
          {computation = right}
          {n = m} {o = returned Z′ Q′}
          (right-stable simulation)
          terminal-return simulated-eq n))
      (terminal-stable-at-right-sum
          {computation = right}
          {n = n} {o = returned U′ V′}
          (right-stable simulation)
          terminal-return right-eq m)
same-index-returned-compatible
    {U′ = U′} {V′ = V′} {right = right}
    simulation {n} left-eq right-eq
    | m , Z′ , Q′ , S , R≤S , simulated-eq , V~Q′
    | refl =
  S , R≤S , V~Q′

same-index-returned-joined :
  ∀ {W W′ U U′ V V′}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  ∀ {n} →
  left n ≡ returned U V →
  right n ≡ returned U′ V′ →
  JoinedValues.Joined U V U′ V′
same-index-returned-joined simulation left-eq right-eq
    with same-index-returned-compatible
      simulation left-eq right-eq
same-index-returned-joined simulation left-eq right-eq
    | S , R≤S , V~V′ =
  JoinedValues.joined (S , V~V′)
