module Simulation.Coercion.InterpreterCoercionQuotientUntagSimulation where

-- File Charter:
--   * EXPERIMENTAL (O34): quotient untagging still uses the old unindexed
--     ground-decision equation and awaits executable-runtime readiness.
--   * Public paired-untag simulation for quotient-framed tagged values.
--   * Makes both successful payload synchronization and synchronized blame
--     explicit in one terminal theorem.
--   * Delegates the reduction-free proof to a private module.

open import Coercions renaming (_？ to _？ᶜ)
open import ImprecisionWf using
  (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterQuotientValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterValueNarrowing using (ValueScoped)
import NuTermImprecision as NTI
open import Types
import proof.InterpreterCoercionQuotientUntagSimulationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-quotient-untag-simulation :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ θ θ′ G H K L σ σ′ V V′ U U′}
    {R : WorldRelation W W′}
    {gG : Ground G} {gH : Ground H}
    {gK : Ground K} {gL : Ground L} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  Φ ∣ Δᴸ ⊢ G ⊑ H ⊣ Δᴿ →
  InterpreterQuotientValueFrame R U U′
    (tagged gK σ V) (tagged gL σ′ V′) →
  ValueScoped W V →
  ValueScoped W′ V′ →
  ValueNarrowing R U U′ →
  TerminalSimulation ValueNarrowing R
    (coerceValue W θ (G ？ᶜ) (tagged gK σ V))
    (coerceValue W′ θ′ (H ？ᶜ) (tagged gL σ′ V′))
paired-quotient-untag-simulation
    {gG = gG} {gH = gH} {gK = gK} {gL = gL}
    runtime G~H frame V-ok V′-ok U~U′ =
  Proof.paired-quotient-untag-simulation
    {gG = gG} {gH = gH} {gK = gK} {gL = gL}
    runtime G~H frame V-ok V′-ok U~U′
