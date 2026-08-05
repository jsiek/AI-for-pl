module Simulation.Indexed.InterpreterIndexedSimulation where

-- File Charter:
--   * Defines the fuel-local core of constructive terminal simulation.
--   * Keeps the triggering interpreter index explicit so the mutual driver
--     can recurse only at a strictly smaller index.
--   * Reassembles the public unbounded `TerminalSimulation` from its indexed
--     observations, stability, and error-freedom proofs.
--   * Contains no interpreter recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
import Data.Empty
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
import Level

open import Interpreter
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

ForwardReturnSimulation :
  ∀ {W W′} →
  ValueResultRelation →
  WorldRelation W W′ →
  Computation →
  Computation →
  StepIndex →
  Set₁
ForwardReturnSimulation value-result R left right left-index =
  ∀ {U V} →
  left left-index ≡ returned U V →
  Σ[ m ∈ StepIndex ]
  Σ[ U′ ∈ World ]
  Σ[ V′ ∈ Value ]
  Σ[ S ∈ WorldRelation U U′ ]
    WorldExtension R S ×
    right m ≡ returned U′ V′ ×
    value-result S V V′

BackwardReturnSimulation :
  ∀ {W W′} →
  ValueResultRelation →
  WorldRelation W W′ →
  Computation →
  Computation →
  StepIndex →
  Set₁
BackwardReturnSimulation value-result R left right right-index =
  ∀ {U′ V′} →
  right right-index ≡ returned U′ V′ →
  (Σ[ m ∈ StepIndex ]
   Σ[ U ∈ World ]
   Σ[ V ∈ Value ]
   Σ[ S ∈ WorldRelation U U′ ]
     WorldExtension R S ×
     left m ≡ returned U V ×
     value-result S V V′)
  ⊎
  (Σ[ m ∈ StepIndex ]
   Σ[ U ∈ World ]
     left m ≡ blamed U)

TargetBlameSimulation :
  ∀ {W W′} →
  WorldRelation W W′ →
  Computation →
  Computation →
  StepIndex →
  Set
TargetBlameSimulation R left right right-index =
  ∀ {U′} →
  right right-index ≡ blamed U′ →
  Σ[ m ∈ StepIndex ]
  Σ[ U ∈ World ]
    left m ≡ blamed U

data TerminalDirection : Set where
  forward-direction :
    TerminalDirection
  backward-direction :
    TerminalDirection
  target-blame-direction :
    TerminalDirection

direction-level :
  TerminalDirection →
  Level.Level
direction-level forward-direction =
  Level.suc Level.zero
direction-level backward-direction =
  Level.suc Level.zero
direction-level target-blame-direction =
  Level.zero

DirectionalObservation :
  ∀ {W W′} →
  (direction : TerminalDirection) →
  ValueResultRelation →
  WorldRelation W W′ →
  Computation →
  Computation →
  (index : StepIndex) →
  Set (direction-level direction)
DirectionalObservation forward-direction value-result R left right =
  ForwardReturnSimulation value-result R left right
DirectionalObservation backward-direction value-result R left right =
  BackwardReturnSimulation value-result R left right
DirectionalObservation target-blame-direction value-result R left right =
  TargetBlameSimulation R left right

record IndexedTerminalSimulation
    {W W′ : World}
    (value-result : ValueResultRelation)
    (R : WorldRelation W W′)
    (left right : Computation)
    (left-index right-index : StepIndex) : Set₂ where
  field
    forward-return :
      ForwardReturnSimulation
        value-result R left right left-index

    backward-return :
      BackwardReturnSimulation
        value-result R left right right-index

    target-blame-reflects :
      TargetBlameSimulation R left right right-index

open IndexedTerminalSimulation public

indexed-directions :
  ∀ {W W′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right left-index right-index} →
  ForwardReturnSimulation
    value-result R left right left-index →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
indexed-directions forward backward blame =
  record
    { forward-return = forward
    ; backward-return = backward
    ; target-blame-reflects = blame
    }

indexed-direction :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (direction : TerminalDirection) →
  IndexedTerminalSimulation value-result R left right index index →
  DirectionalObservation direction value-result R left right index
indexed-direction forward-direction simulation =
  forward-return simulation
indexed-direction backward-direction simulation =
  backward-return simulation
indexed-direction target-blame-direction simulation =
  target-blame-reflects simulation

terminal-simulation-index :
  ∀ {W W′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right left-index right-index} →
  TerminalSimulation value-result R left right →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
terminal-simulation-index simulation =
  record
    { forward-return = TerminalSimulation.forward-return simulation
    ; backward-return = TerminalSimulation.backward-return simulation
    ; target-blame-reflects =
        TerminalSimulation.target-blame-reflects simulation
    }

indexed-terminal-simulation :
  ∀ {W W′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index right-index) →
  TerminalStable left →
  TerminalStable right →
  (∀ {n U e} → left n ≡ failed U e → Data.Empty.⊥) →
  (∀ {n U′ e} → right n ≡ failed U′ e → Data.Empty.⊥) →
  TerminalSimulation value-result R left right
indexed-terminal-simulation indexed left-stable right-stable
    left-error-free right-error-free =
  record
    { left-stable = left-stable
    ; right-stable = right-stable
    ; forward-return =
        λ { {n} eq → forward-return (indexed n n) eq }
    ; backward-return =
        λ { {n} eq → backward-return (indexed n n) eq }
    ; target-blame-reflects =
        λ { {n} eq → target-blame-reflects (indexed n n) eq }
    ; left-error-impossible = left-error-free
    ; right-error-impossible = right-error-free
    }

directional-terminal-simulation :
  ∀ {W W′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right} →
  (∀ left-index →
    ForwardReturnSimulation
      value-result R left right left-index) →
  (∀ right-index →
    BackwardReturnSimulation
      value-result R left right right-index) →
  (∀ right-index →
    TargetBlameSimulation R left right right-index) →
  TerminalStable left →
  TerminalStable right →
  (∀ {n U e} → left n ≡ failed U e → Data.Empty.⊥) →
  (∀ {n U′ e} → right n ≡ failed U′ e → Data.Empty.⊥) →
  TerminalSimulation value-result R left right
directional-terminal-simulation forward backward blame
    left-stable right-stable left-error-free right-error-free =
  indexed-terminal-simulation
    (λ left-index right-index →
      indexed-directions
        (forward left-index)
        (backward right-index)
        (blame right-index))
    left-stable right-stable left-error-free right-error-free
