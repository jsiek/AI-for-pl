module proof.InterpreterCoercionQuotientUntagSimulationProof where

-- File Charter:
--   * EXPERIMENTAL (O34): this proof still contains the superseded
--     environment-free ground-decision helper and is not an active theorem.
--   * Simulates paired `untag` directly on quotient-framed tagged values.
--   * Uses quotient tag observation for both successful payload returns and
--     synchronized blame.
--   * Contains only explicit interpreter equations and no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)

open import Coercions renaming (_？ to _？ᶜ)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Simulation.Coercion.InterpreterCoercionComputation
open import Simulation.Coercion.InterpreterQuotientValueElimination
open import Narrowing.InterpreterQuotientValueNarrowing
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTagNarrowing
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization using
  (TypeEnvironmentRealization)
open import Narrowing.InterpreterValueNarrowing using (ValueScoped)
import NuTermImprecision as NTI
open import proof.InterpreterSimulationHelpers using
  (immediate-blame-simulation; immediate-return-simulation)
open import proof.InterpreterSimulationTransport using
  (simulation-pointwise)
open import Types

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

ground?-exact :
  ∀ {G} →
  (gG : Ground G) →
  ground? G ≡ yes gG
ground?-exact (＇ α) =
  refl
ground?-exact (‵ ι) =
  refl
ground?-exact ★⇒★ =
  refl

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
    {gG = gG} {gH = gH}
    runtime G~H frame V-ok V′-ok U~U′
    with tagOf-narrowing gG gH
      (type-environments-realized runtime) G~H
       | quotient-related-tag-observation
           frame V-ok V′-ok U~U′
paired-quotient-untag-simulation
    {gG = gG} {gH = gH}
    runtime G~H frame V-ok V′-ok U~U′
    | expected , expected′ ,
      expected-eq , expected′-eq , expected~expected′
    | actual , actual′ ,
      actual-eq , actual′-eq , actual~actual′ , V~V′
    with expected ≟Tag actual
paired-quotient-untag-simulation
    {gG = gG} {gH = gH}
    runtime G~H frame V-ok V′-ok U~U′
    | expected , expected′ ,
      expected-eq , expected′-eq , expected~expected′
    | .expected , actual′ ,
      actual-eq , actual′-eq , actual~actual′ , V~V′
    | yes refl =
  simulation-pointwise
    (coerce-untag-computation
      refl (ground?-exact gG) expected-eq actual-eq)
    (coerce-untag-computation
      (tag-match-forward
        expected~expected′ actual~actual′ refl)
      (ground?-exact gH) expected′-eq actual′-eq)
    (immediate-return-simulation V~V′)
paired-quotient-untag-simulation
    {gG = gG} {gH = gH}
    runtime G~H frame V-ok V′-ok U~U′
    | expected , expected′ ,
      expected-eq , expected′-eq , expected~expected′
    | actual , actual′ ,
      actual-eq , actual′-eq , actual~actual′ , V~V′
    | no expected≢actual =
  simulation-pointwise
    (coerce-untag-blame-computation
      expected≢actual (ground?-exact gG) expected-eq actual-eq)
    (coerce-untag-blame-computation
      (λ expected′≡actual′ →
        expected≢actual
          (tag-match-backward
            expected~expected′ actual~actual′
            expected′≡actual′))
      (ground?-exact gH) expected′-eq actual′-eq)
    immediate-blame-simulation
