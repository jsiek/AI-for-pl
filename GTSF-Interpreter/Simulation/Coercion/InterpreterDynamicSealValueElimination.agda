module Simulation.Coercion.InterpreterDynamicSealValueElimination where

-- File Charter:
--   * Public inversion for a source-dynamic sealed semantic value.
--   * Recovers the exact left-dynamic allocation and payload relation.
--   * Delegates exhaustive value-relation inversion to a private module.

open import Interpreter
open import Narrowing.InterpreterTermNarrowing
import proof.InterpreterDynamicSealValueEliminationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

left-dynamic-sealed-payloads :
  ∀ {W W′ α V V′}
    {R : WorldRelation W W′} →
  LeftDynamicSeal R α →
  ValueNarrowing R (sealed α V) V′ →
  ValueNarrowing R V V′
left-dynamic-sealed-payloads =
  Proof.left-dynamic-sealed-payloads
