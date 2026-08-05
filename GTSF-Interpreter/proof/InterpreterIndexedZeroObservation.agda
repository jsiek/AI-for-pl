module proof.InterpreterIndexedZeroObservation where

-- File Charter:
--   * Adjusts indexed terminal simulations at a zero-fuel observation.
--   * Uses only the explicit timeout equation at the endpoint being
--     discarded.
--   * Supports the two asymmetric fuel-induction boundary cases.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
import Data.Nat
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Core.InterpreterOutcome using
  (timed≢blamed; timed≢returned)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

indexed-zero-zero :
  ∀ {W W′ U U′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left Data.Nat.zero ≡ timed U →
  right Data.Nat.zero ≡ timed U′ →
  IndexedTerminalSimulation value-result R left right
    Data.Nat.zero Data.Nat.zero
indexed-zero-zero left-zero right-zero =
  record
    { forward-return =
        λ eq → ⊥-elim (timed≢returned (trans (sym left-zero) eq))
    ; backward-return =
        λ eq → ⊥-elim (timed≢returned (trans (sym right-zero) eq))
    ; target-blame-reflects =
        λ eq → ⊥-elim (timed≢blamed (trans (sym right-zero) eq))
    }

indexed-left-zero :
  ∀ {W W′ U right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left Data.Nat.zero ≡ timed U →
  IndexedTerminalSimulation value-result R left right
    (Data.Nat.suc Data.Nat.zero) right-index →
  IndexedTerminalSimulation value-result R left right
    Data.Nat.zero right-index
indexed-left-zero left-zero simulation =
  record
    { forward-return =
        λ eq → ⊥-elim (timed≢returned (trans (sym left-zero) eq))
    ; backward-return = backward-return simulation
    ; target-blame-reflects = target-blame-reflects simulation
    }

indexed-right-zero :
  ∀ {W W′ U′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right Data.Nat.zero ≡ timed U′ →
  IndexedTerminalSimulation value-result R left right
    left-index (Data.Nat.suc Data.Nat.zero) →
  IndexedTerminalSimulation value-result R left right
    left-index Data.Nat.zero
indexed-right-zero right-zero simulation =
  record
    { forward-return = forward-return simulation
    ; backward-return =
        λ eq → ⊥-elim (timed≢returned (trans (sym right-zero) eq))
    ; target-blame-reflects =
        λ eq → ⊥-elim (timed≢blamed (trans (sym right-zero) eq))
    }
