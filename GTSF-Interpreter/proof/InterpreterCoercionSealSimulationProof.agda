module proof.InterpreterCoercionSealSimulationProof where

-- File Charter:
--   * Instantiates paired seal simulation from relational-store realization.
--   * Shows why static `StoreCorresponds` must be tied to runtime seal links.
--   * Contains no coercion recursion or reduction semantics.

open import Coercions renaming (seal to sealᶜ)
open import Data.Product using (_,_)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
open import Narrowing.InterpreterSealNarrowing using
  (paired-seal-simulation)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI

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
paired-corresponding-seal-simulation runtime corresponds V~V′
    with realizes-store-correspondence
      (store-correspondences-realized runtime) corresponds
paired-corresponding-seal-simulation runtime corresponds V~V′
    | seal , seal′ , left-at , right-at , seal~seal′ =
  paired-seal-simulation
    left-at right-at seal~seal′ V~V′
