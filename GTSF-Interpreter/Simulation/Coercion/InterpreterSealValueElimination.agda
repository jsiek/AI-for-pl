module Simulation.Coercion.InterpreterSealValueElimination where

-- File Charter:
--   * Public structural inversion for paired sealed semantic values.
--   * Recovers the payload relation beneath two related seal wrappers.
--   * Delegates exhaustive value-relation inversion to a private module.
--   * Contains no interpreter computation, reduction, or catch-up theorem.

open import Interpreter
open import Narrowing.InterpreterTermNarrowing
import proof.InterpreterSealValueEliminationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds


paired-sealed-payloads :
  ∀ {W W′ α α′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R (sealed α V) (sealed α′ V′) →
  ValueNarrowing R V V′
paired-sealed-payloads =
  Proof.paired-sealed-payloads

paired-sealed-link :
  ∀ {W W′ α α′ V V′}
    {R : WorldRelation W W′} →
  ValueNarrowing R (sealed α V) (sealed α′ V′) →
  SealLink R α α′
paired-sealed-link =
  Proof.paired-sealed-link
