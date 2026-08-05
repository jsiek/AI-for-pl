module proof.InterpreterDirectionalTransport where

-- File Charter:
--   * Transports each directional terminal observation across pointwise
--     computation equalities and returned-value relation maps.
--   * Keeps the direction explicit so no unused recursive theorem is
--     required.
--   * Contains no interpreter recursion, reduction, or catch-up theorem.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

forward-pointwise :
  ∀ {W W′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (∀ n → left n ≡ left′ n) →
  (∀ n → right n ≡ right′ n) →
  ForwardReturnSimulation
    value-result R left right left-index →
  ForwardReturnSimulation
    value-result R left′ right′ left-index
forward-pointwise left-eq right-eq simulation result-eq
    with simulation
      (trans (left-eq _) result-eq)
forward-pointwise left-eq right-eq simulation result-eq
    | m , U′ , V′ , S , R≤S , right-result , V~V′ =
  m , U′ , V′ , S , R≤S ,
  trans (sym (right-eq m)) right-result , V~V′

backward-pointwise :
  ∀ {W W′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (∀ n → left n ≡ left′ n) →
  (∀ n → right n ≡ right′ n) →
  BackwardReturnSimulation
    value-result R left right right-index →
  BackwardReturnSimulation
    value-result R left′ right′ right-index
backward-pointwise left-eq right-eq simulation result-eq
    with simulation
      (trans (right-eq _) result-eq)
backward-pointwise left-eq right-eq simulation result-eq
    | inj₁
        (m , U , V , S , R≤S , left-result , V~V′) =
  inj₁
    (m , U , V , S , R≤S ,
     trans (sym (left-eq m)) left-result , V~V′)
backward-pointwise left-eq right-eq simulation result-eq
    | inj₂ (m , U , left-result) =
  inj₂
    (m , U , trans (sym (left-eq m)) left-result)

target-blame-pointwise :
  ∀ {W W′ right-index}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (∀ n → left n ≡ left′ n) →
  (∀ n → right n ≡ right′ n) →
  TargetBlameSimulation R left right right-index →
  TargetBlameSimulation R left′ right′ right-index
target-blame-pointwise left-eq right-eq simulation result-eq
    with simulation
      (trans (right-eq _) result-eq)
target-blame-pointwise left-eq right-eq simulation result-eq
    | m , U , left-result =
  m , U , trans (sym (left-eq m)) left-result

forward-result-map :
  ∀ {W W′ left-index}
    {source-result target-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  ForwardReturnSimulation source-result R left right left-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    source-result S V V′ →
    target-result S V V′) →
  ForwardReturnSimulation target-result R left right left-index
forward-result-map simulation result-map result-eq
    with simulation result-eq
forward-result-map simulation result-map result-eq
    | m , U′ , V′ , S , R≤S , right-result , V~V′ =
  m , U′ , V′ , S , R≤S , right-result ,
  result-map R≤S V~V′

backward-result-map :
  ∀ {W W′ right-index}
    {source-result target-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  BackwardReturnSimulation source-result R left right right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    source-result S V V′ →
    target-result S V V′) →
  BackwardReturnSimulation target-result R left right right-index
backward-result-map simulation result-map result-eq
    with simulation result-eq
backward-result-map simulation result-map result-eq
    | inj₁
        (m , U , V , S , R≤S , left-result , V~V′) =
  inj₁
    (m , U , V , S , R≤S , left-result ,
     result-map R≤S V~V′)
backward-result-map simulation result-map result-eq
    | inj₂ blame =
  inj₂ blame

forward-extension-base :
  ∀ {W W′ U U′ left-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {left right : Computation} →
  WorldExtension R S →
  ForwardReturnSimulation
    value-result S left right left-index →
  ForwardReturnSimulation
    value-result R left right left-index
forward-extension-base R≤S simulation result-eq
    with simulation result-eq
forward-extension-base R≤S simulation result-eq
    | m , Z′ , V′ , T , S≤T , right-result , value =
  m , Z′ , V′ , T ,
  ITN.PersistentWorldProperties.world-extension-trans R≤S S≤T ,
  right-result , value

backward-extension-base :
  ∀ {W W′ U U′ right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′}
    {left right : Computation} →
  WorldExtension R S →
  BackwardReturnSimulation
    value-result S left right right-index →
  BackwardReturnSimulation
    value-result R left right right-index
backward-extension-base R≤S simulation result-eq
    with simulation result-eq
backward-extension-base R≤S simulation result-eq
    | inj₁
        (m , Z , V , T , S≤T , left-result , value) =
  inj₁
    (m , Z , V , T ,
     ITN.PersistentWorldProperties.world-extension-trans R≤S S≤T ,
     left-result , value)
backward-extension-base R≤S simulation result-eq
    | inj₂ blame =
  inj₂ blame
