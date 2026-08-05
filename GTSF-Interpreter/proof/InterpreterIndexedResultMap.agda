module proof.InterpreterIndexedResultMap where

-- File Charter:
--   * Maps the returned-value relation of a fuel-local simulation.
--   * Gives the mapper the concrete future-world extension selected by the
--     simulation, so Kripke-indexed certificates can be rebuilt there.
--   * Contains no interpreter recursion or reduction result.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

indexed-result-map :
  ∀ {W W′ left-index right-index}
    {source-result target-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  IndexedTerminalSimulation source-result R left right
    left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    source-result S V V′ →
    target-result S V V′) →
  IndexedTerminalSimulation target-result R left right
    left-index right-index
indexed-result-map simulation map-result =
  record
    { forward-return =
        λ eq →
          let m , U′ , V′ , S , R≤S , right-eq , related =
                forward-return simulation eq
          in m , U′ , V′ , S , R≤S , right-eq ,
             map-result R≤S related
    ; backward-return =
        λ eq →
          Data.Sum.map
            (λ
              { (m , U , V , S , R≤S , left-eq , related) →
                  m , U , V , S , R≤S , left-eq ,
                  map-result R≤S related
              })
            (λ blame → blame)
            (backward-return simulation eq)
    ; target-blame-reflects =
        target-blame-reflects simulation
    }
