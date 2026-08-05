module proof.InterpreterDirectionalSimulation where

-- File Charter:
--   * Recombines one fuel-triggered terminal observation with the impossible
--     observations of a zero-fuel endpoint.
--   * Lets directional fuel inductions reuse the checked indexed sequencing
--     algebra without requesting a same-measure recursive simulation.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Core.InterpreterOutcome using
  (timed≢blamed; timed≢returned)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

indexed-family-forward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index right-index) →
  ForwardReturnSimulation value-result R left right index
indexed-family-forward {index = index} family =
  forward-return (family index zero)

indexed-family-backward :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index right-index) →
  BackwardReturnSimulation value-result R left right index
indexed-family-backward {index = index} family =
  backward-return (family zero index)

indexed-family-target-blame :
  ∀ {W W′ index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  (∀ left-index right-index →
    IndexedTerminalSimulation value-result R left right
      left-index right-index) →
  TargetBlameSimulation R left right index
indexed-family-target-blame {index = index} family =
  target-blame-reflects (family zero index)

forward-at-right-zero :
  ∀ {W W′ U′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed U′ →
  ForwardReturnSimulation
    value-result R left right left-index →
  IndexedTerminalSimulation value-result R left right
    left-index zero
forward-at-right-zero right-zero forward =
  indexed-directions forward
    (λ eq →
      ⊥-elim
        (timed≢returned (trans (sym right-zero) eq)))
    (λ eq →
      ⊥-elim
        (timed≢blamed (trans (sym right-zero) eq)))

backward-at-left-zero :
  ∀ {W W′ U right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed U →
  BackwardReturnSimulation
    value-result R left right right-index →
  TargetBlameSimulation R left right right-index →
  IndexedTerminalSimulation value-result R left right
    zero right-index
backward-at-left-zero left-zero backward blame =
  indexed-directions
    (λ eq →
      ⊥-elim
        (timed≢returned (trans (sym left-zero) eq)))
    backward blame

zero-forward :
  ∀ {W W′ U}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  left zero ≡ timed U →
  ForwardReturnSimulation value-result R left right zero
zero-forward left-zero eq =
  ⊥-elim
    (timed≢returned (trans (sym left-zero) eq))

zero-backward :
  ∀ {W W′ U′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed U′ →
  BackwardReturnSimulation value-result R left right zero
zero-backward right-zero eq =
  ⊥-elim
    (timed≢returned (trans (sym right-zero) eq))

zero-target-blame :
  ∀ {W W′ U′}
    {R : WorldRelation W W′}
    {left right : Computation} →
  right zero ≡ timed U′ →
  TargetBlameSimulation R left right zero
zero-target-blame right-zero eq =
  ⊥-elim
    (timed≢blamed (trans (sym right-zero) eq))
