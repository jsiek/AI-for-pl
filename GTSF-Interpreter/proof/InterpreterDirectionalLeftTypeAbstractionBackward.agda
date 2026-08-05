module proof.InterpreterDirectionalLeftTypeAbstractionBackward where

-- File Charter:
--   * Proves backward return and target-blame simulation for a source-only
--     type abstraction from structurally smaller body simulations.
--   * Uses return uniqueness and blame impossibility of typed syntactic
--     values; it never evaluates an abstraction body while closing it.
--   * Contains no small-step reduction, catch-up result, or DGG theorem.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import ImprecisionWf using
  (_ˣ⊑★; ⇑ᴸᵢ; ν)
open import Interpreter
open import Runtime.InterpreterAbstractRuntimeFrame
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Framed.InterpreterFramedEnvironmentLift
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Runtime.InterpreterSyntacticValueComputation
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import proof.InterpreterCloseValueTyping using
  (closeValue-defined; syntacticValue-complete)
open import proof.InterpreterClosedValueProof using
  (closeValue-closed; next-abstract-fresh)
open import proof.InterpreterDirectionalLeftTypeAbstractionTerm using
  (left-type-abstraction-close)
open import proof.InterpreterFramedTypeAbstractionProof using
  (type-abstraction-computation-eq)
open import proof.InterpreterLeftTypeAbstractionResult using
  (left-type-abstraction-result)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-source)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


left-type-abstraction-term-backward :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ ρ↑ γᵀ γᵀ↑
      θ θ′ γ γ′ V N′ A B p}
    {{nonvar : ImprecisionWf.NonVar A}}
    {occ : occurs zero A ≡ true}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (store :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑) →
  (context :
    NTI.LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑) →
  (vV : N.Value V) →
  (termV : InterpreterTerm V) →
  (termN′ : InterpreterTerm N′) →
  (body :
    AlignedInterpreterTermNarrowing
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (origins : FramedEnvironmentNarrowing runtime γᵀ γ γ′) →
  (∀ body-index →
    FramedDirectionalInterpreterTermSimulation
      backward-direction body-index
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  BackwardReturnSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar occ p)) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ N′) index
left-type-abstraction-term-backward
    {index = zero}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation ()
left-type-abstraction-term-backward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    with syntacticValue-complete vV
left-type-abstraction-term-backward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    with closeValue-defined
      (left-runtime-context
        (left-abstract-runtime
          {X = nextAbstractName θ} runtime store))
      (left-environment-typed
        (left-abstract-environment-realization
          {X = nextAbstractName θ}
          {runtime↑ =
            left-abstract-runtime
              {X = nextAbstractName θ} runtime store}
          context environment))
      termV source-value
      (TT.forget
        (open-interpreter-narrowing-source-typing
          (open-interpreter-narrowing {R = R} body)))
left-type-abstraction-term-backward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    with body-simulation (suc index)
      (assumption-membership-unique-source unique)
      (left-abstract-runtime
        {X = nextAbstractName θ} runtime store)
      (left-abstract-environment-realization
        {X = nextAbstractName θ}
        {runtime↑ =
          left-abstract-runtime
            {X = nextAbstractName θ} runtime store}
        context environment)
      (left-abstract-framed-environment-lift
        unique context origins)
      (open-interpreter-narrowing {R = R} body)
      result-eq
left-type-abstraction-term-backward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | inj₁
      (m , source-world , source-returned , relation ,
       R≤S , source-return , body-result)
    with syntactic-value-return-unique
      {W = W} {U = source-world}
      {γ = γ}
      {θ = abstract-name (nextAbstractName θ) ∷ θ}
      {M = V} {V = source-result}
      {V′ = source-returned} {n = m}
      source-value source-close source-return
left-type-abstraction-term-backward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | inj₁
      (m , .W , .source-result , relation ,
       R≤S , source-return , body-result)
    | refl , refl =
  inj₁
    ( suc zero
    , W
    , type-abstraction (nextAbstractName θ) source-result
    , relation
    , R≤S
    , type-abstraction-computation-eq
        source-value source-decision
        (left-type-abstraction-close
          {γ = γ} {θ = θ} {vV = source-value}
          source-close)
        (suc zero)
    , left-type-abstraction-result
        store context source-value termV termN′ body
        environment (next-abstract-fresh θ)
        (closeValue-closed
          {γ = γ}
          {θ = abstract-name (nextAbstractName θ) ∷ θ}
          source-value source-close)
        R≤S body-result
    )
left-type-abstraction-term-backward
    {index = suc index} {W} {θ = θ} {γ = γ} {V = V}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | inj₂ (m , source-world , source-blame) =
  ⊥-elim
    (syntactic-value-never-blames
      {W = W} {U = source-world}
      {γ = γ}
      {θ = abstract-name (nextAbstractName θ) ∷ θ}
      {M = V} {n = m}
      source-value source-blame)


left-type-abstraction-term-target-blame :
  ∀ {index W W′ Φ Δᴸ Δᴿ ρ ρ↑ γᵀ γᵀ↑
      θ θ′ γ γ′ V N′ A B p}
    {{nonvar : ImprecisionWf.NonVar A}}
    {occ : occurs zero A ≡ true}
    {R : WorldRelation W W′}
    {runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′} →
  AssumptionMembershipUnique Φ →
  (store :
    NTI.LiftLeftStoreⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ↑) →
  (context :
    NTI.LiftLeftCtxⁱ
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) γᵀ γᵀ↑) →
  (vV : N.Value V) →
  (termV : InterpreterTerm V) →
  (termN′ : InterpreterTerm N′) →
  (body :
    AlignedInterpreterTermNarrowing
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  (origins : FramedEnvironmentNarrowing runtime γᵀ γ γ′) →
  (∀ body-index →
    FramedDirectionalInterpreterTermSimulation
      target-blame-direction body-index
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  TargetBlameSimulation R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ N′) index
left-type-abstraction-term-target-blame
    {index = zero}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation ()
left-type-abstraction-term-target-blame
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation blame-eq
    with body-simulation (suc index)
      (assumption-membership-unique-source unique)
      (left-abstract-runtime
        {X = nextAbstractName θ} runtime store)
      (left-abstract-environment-realization
        {X = nextAbstractName θ}
        {runtime↑ =
          left-abstract-runtime
            {X = nextAbstractName θ} runtime store}
        context environment)
      (left-abstract-framed-environment-lift
        unique context origins)
      (open-interpreter-narrowing {R = R} body)
      blame-eq
left-type-abstraction-term-target-blame
    {index = suc index} {W} {θ = θ} {γ = γ} {V = V}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation blame-eq
    | m , source-world , source-blame =
  ⊥-elim
    (syntactic-value-never-blames
      {W = W} {U = source-world}
      {γ = γ}
      {θ = abstract-name (nextAbstractName θ) ∷ θ}
      {M = V} {n = m}
      vV source-blame)
