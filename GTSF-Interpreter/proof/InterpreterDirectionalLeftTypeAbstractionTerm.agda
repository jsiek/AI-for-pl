module proof.InterpreterDirectionalLeftTypeAbstractionTerm where

-- File Charter:
--   * Proves the source-only type-abstraction term case in all three terminal
--     directions from a structural body simulation at the same fuel index.
--   * Closes the source body below the generated abstract name and wraps each
--     exact body result with its future seal-instantiation certificate.
--   * Uses no recursive call on fuel, small-step reduction, or catch-up result.

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Maybe using (just)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes)

open import ImprecisionWf using
  (_ˣ⊑★; ⇑ᴸᵢ; ν)
open import Interpreter
open import Runtime.InterpreterAbstractRuntimeFrame
open import Runtime.InterpreterClosedValue
open import Simulation.Directional.InterpreterDirectionalSimulationMotive
open import Simulation.Framed.InterpreterFramedEnvironmentLift
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Typing.InterpreterSemanticTypingCore using (⟦_⟧[_])
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Runtime.InterpreterSyntacticValueComputation
open import Runtime.InterpreterSyntacticValueTermination
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import proof.InterpreterCloseValueTyping using
  (closeValue-defined; syntacticValue-complete)
open import proof.InterpreterClosedValueProof using
  (closeValue-closed; next-abstract-fresh)
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

left-type-abstraction-close :
  ∀ {γ θ V U}
    {vV : N.Value V} →
  closeValue vV γ
    (abstract-name (nextAbstractName θ) ∷ θ) ≡ just U →
  closeValue (N.Λ vV) γ θ ≡
    just (type-abstraction (nextAbstractName θ) U)
left-type-abstraction-close close-eq
    rewrite close-eq =
  refl


left-type-abstraction-term-forward :
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
      forward-direction body-index
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ ρ↑ γᵀ↑ V N′ A B p) →
  ForwardReturnSimulation
    (FramedValueResult ρ θ θ′ (ν nonvar occ p)) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ N′) index
left-type-abstraction-term-forward
    {index = zero}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation ()
left-type-abstraction-term-forward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    with syntacticValue-complete vV
left-type-abstraction-term-forward
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
left-type-abstraction-term-forward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    with syntactic-value-return-unique
      {W = W} {γ = γ} {θ = θ}
      {M = N.Λ V}
      {V = type-abstraction (nextAbstractName θ) source-result}
      {n = suc index}
      (N.Λ source-value)
      (left-type-abstraction-close
        {γ = γ} {θ = θ} {vV = source-value}
        source-close)
      result-eq
left-type-abstraction-term-forward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | refl , refl
    with typed-syntactic-value-eventually-returns
      (left-runtime-context
        (left-abstract-runtime
          {X = nextAbstractName θ} runtime store))
      source-value
      (TT.forget
        (open-interpreter-narrowing-source-typing
          (open-interpreter-narrowing {R = R} body)))
      source-close
left-type-abstraction-term-forward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | refl , refl
    | body-index , source-return
    with body-simulation body-index
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
      source-return
left-type-abstraction-term-forward
    {index = suc index} {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ} {ρ↑} {γᵀ} {γᵀ↑} {θ} {θ′} {γ} {γ′}
    {V} {N′} {A} {B} {p}
    {{nonvar = nonvar}} {occ = occ} {R = R}
    unique store context vV termV termN′ body
    runtime environment origins body-simulation result-eq
    | source-value , source-decision
    | source-result , source-close
    | refl , refl
    | body-index , source-return
    | m , target-world , target-value , relation ,
      R≤S , target-result , body-result =
  m , target-world , target-value , relation ,
  R≤S , target-result ,
  left-type-abstraction-result
    store context source-value termV termN′ body
    environment (next-abstract-fresh θ)
    (closeValue-closed
      {γ = γ}
      {θ = abstract-name (nextAbstractName θ) ∷ θ}
      source-value source-close)
    R≤S body-result
