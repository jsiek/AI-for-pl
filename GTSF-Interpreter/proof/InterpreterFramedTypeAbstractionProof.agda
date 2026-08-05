module proof.InterpreterFramedTypeAbstractionProof where

-- File Charter:
--   * Proves exact indexed paired type-abstraction simulation.
--   * Peels proof-only static prefixes only to recover value witnesses.
--   * Closes values in the original ambient runtime and environment.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just)
open import Data.Product using (_,_; Σ-syntax)
import Data.Nat
open import Relation.Nullary using (yes)

open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import Interpreter
open import Runtime.InterpreterCloseFramedValue using (close-aligned-framed)
open import Runtime.InterpreterClosedValue
open import Narrowing.InterpreterFramedValueNarrowing
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import proof.InterpreterCloseValueTyping using
  (closeValue-defined; syntacticValue-complete)
open import proof.InterpreterClosedValueProof using (closeValue-closed)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
open import
  proof.NuImprecisionAssumptionMembershipUniquenessDef using
  (AssumptionMembershipUnique)
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

type-abstraction-computation-eq :
  ∀ {W γ θ V U}
    (vV : N.Value V) →
  syntacticValue? V ≡ yes vV →
  closeValue (N.Λ vV) γ θ ≡ just U →
  ∀ n →
  interpret W γ θ (N.Λ V) n ≡ immediateReturn W U n
type-abstraction-computation-eq vV decision-eq close-eq
    Data.Nat.zero =
  refl
type-abstraction-computation-eq vV decision-eq close-eq
    (Data.Nat.suc n)
    rewrite decision-eq | close-eq =
  refl

paired-type-abstraction-values :
  ∀ {Φ Δᴸ Δᴿ ρ γᵀ V V′ A B p}
    (alignment :
      AlignedInterpreterTermNarrowing
        Φ Δᴸ Δᴿ ρ γᵀ
        (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  Σ[ vV ∈ N.Value V ] N.Value V′
paired-type-abstraction-values
    (paired-type-abstraction-aligned
      store context vV vV′ termV termV′ body)
    refl =
  vV , vV′
paired-type-abstraction-values
    (left-type-abstraction-aligned
      occ store context vV termV termN′ body)
    ()
paired-type-abstraction-values
    (allocation-prefix-aligned prefix body source target)
    root =
  paired-type-abstraction-values body root

indexed-framed-paired-type-abstraction :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  AssumptionMembershipUnique Φ →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  FramedEnvironmentNarrowing runtime γᵀ γ γ′ →
  IndexedTerminalSimulation
    (FramedValueResult ρ θ θ′ p) R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′))
    left-index right-index
indexed-framed-paired-type-abstraction
    unique alignment root runtime environment origins
    with paired-type-abstraction-values alignment root
indexed-framed-paired-type-abstraction
    {V = V} {V′} {R = R}
    unique alignment root runtime environment origins
    | source-syntax , target-syntax =
  indexed-simulation-pointwise
    (type-abstraction-computation-eq
      source-value source-decision source-close)
    (type-abstraction-computation-eq
      target-value target-decision target-close)
    (terminal-simulation-index
      (immediate-return-simulation
        (framed-result runtime
          (close-aligned-framed
            unique alignment runtime environment origins
            (closeValue-closed (N.Λ source-value) source-close)
            (closeValue-closed (N.Λ target-value) target-close)))))
  where
  source-value =
    Data.Product.proj₁ (syntacticValue-complete source-syntax)

  source-decision =
    Data.Product.proj₂ (syntacticValue-complete source-syntax)

  target-value =
    Data.Product.proj₁ (syntacticValue-complete target-syntax)

  target-decision =
    Data.Product.proj₂ (syntacticValue-complete target-syntax)

  terms =
    open-interpreter-narrowing {R = R} alignment

  source-close =
    Data.Product.proj₂
      (closeValue-defined
        (left-runtime-context runtime)
        (left-environment-typed environment)
        (interpreter-narrowing-source-term
          (aligned-term-shape alignment))
        (N.Λ source-value)
        (TT.forget
          (open-interpreter-narrowing-source-typing terms)))

  target-close =
    Data.Product.proj₂
      (closeValue-defined
        (right-runtime-context runtime)
        (right-environment-typed environment)
        (interpreter-narrowing-target-term
          (aligned-term-shape alignment))
        (N.Λ target-value)
        (TT.forget
          (open-interpreter-narrowing-target-typing terms)))
