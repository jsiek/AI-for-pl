module Simulation.Coercion.InterpreterCoercionSealSimulation where

-- File Charter:
--   * Public paired seal simulation from static store correspondence.
--   * States the runtime synchronization requirement at the use site.
--   * Delegates the reduction-free proof to a focused proof module.

open import Coercions renaming (seal to sealᶜ)
open import Interpreter
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import proof.InterpreterCoercionSealSimulationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-corresponding-seal-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ α A β B p V V′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  NTI.StoreCorresponds ρ α A β B p →
  ValueNarrowing R V V′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (sealᶜ A α) V)
    (coerceValue W′ θ′ (sealᶜ B β) V′)
paired-corresponding-seal-simulation =
  Proof.paired-corresponding-seal-simulation
