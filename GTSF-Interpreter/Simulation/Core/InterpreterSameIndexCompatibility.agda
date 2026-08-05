module Simulation.Core.InterpreterSameIndexCompatibility where

-- File Charter:
--   * Relates two returns observed at the same fuel index from any
--     constructive terminal simulation.
--   * Exposes the concrete joined-value corollary used by interpreter DGG.
--   * Uses terminal stabilization and computation determinism, not catch-up
--     or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; Σ-syntax)

open import Interpreter
import DGG.InterpreterJoined as JoinedDefinition
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
import proof.InterpreterSameIndexCompatibilityProof as Proof

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
same-index-returned-compatible =
  Proof.same-index-returned-compatible

same-index-returned-joined :
  ∀ {W W′ U U′ V V′}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  ∀ {n} →
  left n ≡ returned U V →
  right n ≡ returned U′ V′ →
  JoinedValues.Joined U V U′ V′
same-index-returned-joined =
  Proof.same-index-returned-joined
