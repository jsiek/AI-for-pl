module Simulation.Core.InterpreterSimulationResult where

-- File Charter:
--   * Defines the constructive result interface for direct interpreter
--     simulation.
--   * Makes eventual synchronized returns, permitted source blame, reflected
--     target blame, and impossible interpreter errors explicit.
--   * Contains no evaluator proof, catch-up theorem, or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
import Data.Empty
import Data.Nat
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)

open import Interpreter
open import Core.InterpreterOutcome using (Terminal)
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

Computation : Set
Computation = StepIndex → Outcome

fixedOutcome :
  Outcome →
  Computation
fixedOutcome o n =
  o

chain :
  Computation →
  (World → Value → Computation) →
  Computation
chain head continuation n =
  head n >>= λ U V → continuation U V n

guard :
  World →
  Computation →
  Computation
guard W computation Data.Nat.zero =
  timed W
guard W computation (Data.Nat.suc n) =
  computation n

sequence :
  World →
  Computation →
  (World → Value → Computation) →
  Computation
sequence W head continuation =
  guard W (chain head continuation)

immediateReturn :
  World →
  Value →
  Computation
immediateReturn W V Data.Nat.zero =
  timed W
immediateReturn W V (Data.Nat.suc n) =
  returned W V

immediateBlame :
  World →
  Computation
immediateBlame W Data.Nat.zero =
  timed W
immediateBlame W (Data.Nat.suc n) =
  blamed W

TerminalStable : Computation → Set
TerminalStable computation =
  ∀ {n o} →
  Terminal o →
  computation n ≡ o →
  (k : StepIndex) →
  computation (n Data.Nat.+ k) ≡ o

ValueResultRelation : Set₂
ValueResultRelation =
  ∀ {W W′} →
  WorldRelation W W′ →
  Value → Value → Set₁

data SameIndexSimulation
    {W W′ : World}
    (value-result : ValueResultRelation)
    (R : WorldRelation W W′) :
    Outcome → Outcome → Set₁ where
  paired-timeout :
    ∀ {U U′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    SameIndexSimulation value-result R (timed U) (timed U′)

  synchronized-return :
    ∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    value-result S V V′ →
    SameIndexSimulation value-result R
      (returned U V) (returned U′ V′)

  permitted-source-blame :
    ∀ {U o′} →
    SameIndexSimulation value-result R (blamed U) o′

record TerminalSimulation
    {W W′ : World}
    (value-result : ValueResultRelation)
    (R : WorldRelation W W′)
    (left right : Computation) : Set₂ where
  field
    left-stable :
      TerminalStable left

    right-stable :
      TerminalStable right

    forward-return :
      ∀ {n U V} →
      left n ≡ returned U V →
      Σ[ m ∈ StepIndex ]
      Σ[ U′ ∈ World ]
      Σ[ V′ ∈ Value ]
      Σ[ S ∈ WorldRelation U U′ ]
        WorldExtension R S ×
        right m ≡ returned U′ V′ ×
        value-result S V V′

    backward-return :
      ∀ {n U′ V′} →
      right n ≡ returned U′ V′ →
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

    target-blame-reflects :
      ∀ {n U′} →
      right n ≡ blamed U′ →
      Σ[ m ∈ StepIndex ]
      Σ[ U ∈ World ]
        left m ≡ blamed U

    left-error-impossible :
      ∀ {n U e} →
      left n ≡ failed U e →
      Data.Empty.⊥

    right-error-impossible :
      ∀ {n U′ e} →
      right n ≡ failed U′ e →
      Data.Empty.⊥

open TerminalSimulation public
