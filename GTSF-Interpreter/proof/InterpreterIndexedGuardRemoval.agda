module proof.InterpreterIndexedGuardRemoval where

-- File Charter:
--   * Removes explicit fuel guards from indexed terminal simulations.
--   * Converts every matching guarded terminal witness back to an
--     unguarded witness by inverting its necessarily positive index.
--   * Supports paired and one-sided guarded computations.
--   * Contains no interpreter recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

remove-right-return-guard :
  ∀ {W right m U V} →
  guard W right m ≡ returned U V →
  Data.Product.Σ StepIndex
    (λ n → right n ≡ returned U V)
remove-right-return-guard {m = zero} eq =
  ⊥-elim (timed≢returned eq)
remove-right-return-guard {m = suc n} eq =
  n , eq

remove-right-blame-guard :
  ∀ {W right m U} →
  guard W right m ≡ blamed U →
  Data.Product.Σ StepIndex
    (λ n → right n ≡ blamed U)
remove-right-blame-guard {m = zero} eq =
  ⊥-elim (timed≢blamed eq)
remove-right-blame-guard {m = suc n} eq =
  n , eq

remove-both-guards :
  ∀ {W W′ left-index right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  IndexedTerminalSimulation value-result R
    (guard W left) (guard W′ right)
    (suc left-index) (suc right-index) →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
remove-both-guards
    {W = W} {W′ = W′} {left = left} {right = right}
    simulation =
  record
    { forward-return =
        λ eq →
          let
            m , U′ , V′ , S , R≤S , guarded-eq , V~V′ =
              forward-return simulation eq
            q , right-eq =
              remove-right-return-guard
                {W = W′} {right = right} {m = m} guarded-eq
          in
          q , U′ , V′ , S , R≤S , right-eq , V~V′
    ; backward-return =
        λ eq →
          Data.Sum.map
            (λ
              { (m , U , V , S , R≤S , guarded-eq , V~V′) →
                  let q , left-eq =
                        remove-right-return-guard
                          {W = W} {right = left} {m = m} guarded-eq
                  in q , U , V , S , R≤S , left-eq , V~V′
              })
            (λ
              { (m , U , guarded-eq) →
                  let q , left-eq =
                        remove-right-blame-guard
                          {W = W} {right = left} {m = m} guarded-eq
                  in q , U , left-eq
              })
            (backward-return simulation eq)
    ; target-blame-reflects =
        λ eq →
          let
            m , U , guarded-eq =
              target-blame-reflects simulation eq
            q , left-eq =
              remove-right-blame-guard
                {W = W} {right = left} {m = m} guarded-eq
          in
          q , U , left-eq
    }

remove-right-guard :
  ∀ {W W′ left-index right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  IndexedTerminalSimulation value-result R
    left (guard W′ right) left-index (suc right-index) →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
remove-right-guard
    {W′ = W′} {right = right}
    simulation =
  record
    { forward-return =
        λ eq →
          let
            m , U′ , V′ , S , R≤S , guarded-eq , V~V′ =
              forward-return simulation eq
            q , right-eq =
              remove-right-return-guard
                {W = W′} {right = right} {m = m} guarded-eq
          in
          q , U′ , V′ , S , R≤S , right-eq , V~V′
    ; backward-return = backward-return simulation
    ; target-blame-reflects = target-blame-reflects simulation
    }

remove-left-guard :
  ∀ {W W′ left-index right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  IndexedTerminalSimulation value-result R
    (guard W left) right (suc left-index) right-index →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
remove-left-guard
    {W = W} {left = left}
    simulation =
  record
    { forward-return = forward-return simulation
    ; backward-return =
        λ eq →
          Data.Sum.map
            (λ
              { (m , U , V , S , R≤S , guarded-eq , V~V′) →
                  let q , left-eq =
                        remove-right-return-guard
                          {W = W} {right = left} {m = m} guarded-eq
                  in q , U , V , S , R≤S , left-eq , V~V′
              })
            (λ
              { (m , U , guarded-eq) →
                  let q , left-eq =
                        remove-right-blame-guard
                          {W = W} {right = left} {m = m} guarded-eq
                  in q , U , left-eq
              })
            (backward-return simulation eq)
    ; target-blame-reflects =
        λ eq →
          let
            m , U , guarded-eq =
              target-blame-reflects simulation eq
            q , left-eq =
              remove-right-blame-guard
                {W = W} {right = left} {m = m} guarded-eq
          in
          q , U , left-eq
    }
