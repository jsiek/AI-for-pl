module proof.InterpreterIndexedGuardSimulation where

-- File Charter:
--   * Lifts fuel-local simulation through paired and one-sided guards.
--   * Advances exactly the endpoint whose direct interpreter call consumes
--     the additional constructor fuel.
--   * Contains no evaluator recursion or reduction semantics.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Function.Base using (case_of_)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

paired-guard-indexed :
  ∀ {W W′ U U′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation}
    {left-index right-index} →
  IndexedTerminalSimulation value-result R left right
    left-index right-index →
  IndexedTerminalSimulation value-result R
    (guard U left) (guard U′ right)
    (suc left-index) (suc right-index)
paired-guard-indexed simulation =
  record
    { forward-return =
        λ eq →
          let m , Z′ , V′ , S , R≤S , right-eq , V~V′ =
                forward-return simulation eq
          in suc m , Z′ , V′ , S , R≤S , right-eq , V~V′
    ; backward-return =
        λ eq →
          case backward-return simulation eq of λ
            { (inj₁
                (m , Z , V , S , R≤S , left-eq , V~V′)) →
                inj₁
                  (suc m , Z , V , S , R≤S , left-eq , V~V′)
            ; (inj₂ (m , Z , left-eq)) →
                inj₂ (suc m , Z , left-eq)
            }
    ; target-blame-reflects =
        λ eq →
          let m , Z , left-eq =
                target-blame-reflects simulation eq
          in suc m , Z , left-eq
    }

left-guard-indexed :
  ∀ {W W′ U} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation}
    {left-index right-index} →
  IndexedTerminalSimulation value-result R left right
    left-index right-index →
  IndexedTerminalSimulation value-result R
    (guard U left) right (suc left-index) right-index
left-guard-indexed simulation =
  record
    { forward-return = forward-return simulation
    ; backward-return =
        λ eq →
          case backward-return simulation eq of λ
            { (inj₁
                (m , Z , V , S , R≤S , left-eq , V~V′)) →
                inj₁
                  (suc m , Z , V , S , R≤S , left-eq , V~V′)
            ; (inj₂ (m , Z , left-eq)) →
                inj₂ (suc m , Z , left-eq)
            }
    ; target-blame-reflects =
        λ eq →
          let m , Z , left-eq =
                target-blame-reflects simulation eq
          in suc m , Z , left-eq
    }

right-guard-indexed :
  ∀ {W W′ U′} {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation}
    {left-index right-index} →
  IndexedTerminalSimulation value-result R left right
    left-index right-index →
  IndexedTerminalSimulation value-result R
    left (guard U′ right) left-index (suc right-index)
right-guard-indexed simulation =
  record
    { forward-return =
        λ eq →
          let m , Z′ , V′ , S , R≤S , right-eq , V~V′ =
                forward-return simulation eq
          in suc m , Z′ , V′ , S , R≤S , right-eq , V~V′
    ; backward-return = backward-return simulation
    ; target-blame-reflects = target-blame-reflects simulation
    }
