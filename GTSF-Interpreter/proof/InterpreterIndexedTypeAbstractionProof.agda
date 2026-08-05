module proof.InterpreterIndexedTypeAbstractionProof where

-- File Charter:
--   * Proves indexed paired type-abstraction simulation by explicit closing.
--   * Peels proof-only allocation prefixes while preserving the executable
--     runtime frame.
--   * Uses interpreter equations, typing, and closing metatheory only.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
import Data.Nat
open import Relation.Nullary using (yes)

open import Interpreter
open import Runtime.InterpreterCloseOperationalValue
open import Runtime.InterpreterClosedValue
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Narrowing.InterpreterOperationalValueNarrowing
open import Typing.InterpreterSemanticTypingCore
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationResult using (immediateReturn)
open import Narrowing.InterpreterTermNarrowing
import NuTermImprecision as NTI
import NuTerms as N
import TermTyping as TT
open import proof.InterpreterCloseValueTyping using
  (closeValue-defined; syntacticValue-complete)
open import proof.InterpreterClosedValueProof using
  (closeValue-closed)
open import proof.InterpreterIndexedSimulationTransport using
  (indexed-simulation-pointwise)
open import proof.InterpreterRuntimeFramePrefix using
  (runtime-frame-prefix)
open import proof.InterpreterSimulationHelpers using
  (immediate-return-simulation)
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

indexed-paired-type-abstraction-simulation :
  ∀ {left-index right-index W W′ Φ Δᴸ Δᴿ ρ γᵀ
      θ θ′ γ γ′ V V′ A B p}
    {R : WorldRelation W W′} →
  (alignment :
    AlignedInterpreterTermNarrowing
      Φ Δᴸ Δᴿ ρ γᵀ
      (N.Λ V) (N.Λ V′) (`∀ A) (`∀ B) p) →
  aligned-term-root alignment ≡ paired-type-abstraction-rootᴬ →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′) →
  (environment : EnvironmentRealization runtime γᵀ γ γ′) →
  OperationalEnvironmentNarrowing θ θ′ R γᵀ γ γ′ →
  IndexedTerminalSimulation
    (OperationalValueResult
      ⟦ `∀ A ⟧[ θ ]
      ⟦ `∀ B ⟧[ θ′ ])
    R
    (interpret W γ θ (N.Λ V))
    (interpret W′ γ′ θ′ (N.Λ V′))
    left-index right-index
indexed-paired-type-abstraction-simulation
    {R = R}
    alignment@(paired-type-abstraction-aligned
      store context vV vV′ termV termV′ body)
    refl runtime environment origins =
  indexed-simulation-pointwise
    (type-abstraction-computation-eq
      left-value left-decision left-close)
    (type-abstraction-computation-eq
      right-value right-decision right-close)
    (terminal-simulation-index
      (immediate-return-simulation
        (close-aligned-operational
          alignment runtime environment origins
          (closeValue-closed (N.Λ left-value) left-close)
          (closeValue-closed (N.Λ right-value) right-close))))
  where
  left-value =
    Data.Product.proj₁ (syntacticValue-complete vV)

  left-decision =
    Data.Product.proj₂ (syntacticValue-complete vV)

  right-value =
    Data.Product.proj₁ (syntacticValue-complete vV′)

  right-decision =
    Data.Product.proj₂ (syntacticValue-complete vV′)

  terms =
    open-interpreter-narrowing {R = R} alignment

  left-close =
    Data.Product.proj₂
      (closeValue-defined
        (left-runtime-context runtime)
        (left-environment-typed environment)
        (interpreter-narrowing-source-term
          (aligned-term-shape alignment))
        (N.Λ left-value)
        (TT.forget
          (open-interpreter-narrowing-source-typing terms)))

  right-close =
    Data.Product.proj₂
      (closeValue-defined
        (right-runtime-context runtime)
        (right-environment-typed environment)
        (interpreter-narrowing-target-term
          (aligned-term-shape alignment))
        (N.Λ right-value)
        (TT.forget
          (open-interpreter-narrowing-target-typing terms)))
indexed-paired-type-abstraction-simulation
    (left-type-abstraction-aligned
      occ store context vV termV termN′ body)
    () runtime environment origins
indexed-paired-type-abstraction-simulation
    (allocation-prefix-aligned prefix body source target)
    root runtime environment origins =
  indexed-paired-type-abstraction-simulation
    body root prefixed-runtime prefixed-environment origins
  where
  prefixed-runtime =
    runtime-narrowing-from-frame
      (left-world-typed runtime)
      (right-world-typed runtime)
      (assumption-membership-unique runtime)
      (runtime-frame-prefix prefix
        (runtime-narrowing-frame runtime))

  prefixed-environment =
    environment-realization
      (environments-narrow environment)
      (left-environment-typed environment)
      (right-environment-typed environment)
