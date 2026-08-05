module proof.InterpreterIndexedSimulationTransport where

-- File Charter:
--   * Transports fuel-local simulations across pointwise computation
--     equations and upgrades value-only returns with unary semantic typing.
--   * Keeps the two observed indices explicit.
--   * Contains no recursive driver or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Typing.InterpreterSemanticTypingCore using
  ( OutcomeTyping
  ; SemanticType
  ; return-typed
  )
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTypedValueNarrowing
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

indexed-simulation-pointwise :
  ∀ {W W′ left-index right-index}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (∀ n → left n ≡ left′ n) →
  (∀ n → right n ≡ right′ n) →
  IndexedTerminalSimulation value-result R left′ right′
    left-index right-index →
  IndexedTerminalSimulation value-result R left right
    left-index right-index
indexed-simulation-pointwise
    {left-index = left-index} {right-index}
    left-eq right-eq simulation =
  record
    { forward-return =
        λ eq →
          let m , U′ , V′ , S , R≤S , target-eq , V~V′ =
                forward-return simulation
                  (trans (sym (left-eq left-index)) eq)
          in m , U′ , V′ , S , R≤S ,
             trans (right-eq m) target-eq , V~V′
    ; backward-return =
        λ eq →
          Data.Sum.map
            (λ
              { (m , U , V , S , R≤S , source-eq , V~V′) →
                  m , U , V , S , R≤S ,
                  trans (left-eq m) source-eq , V~V′
              })
            (λ
              { (m , U , source-eq) →
                  m , U , trans (left-eq m) source-eq
              })
            (backward-return simulation
              (trans (sym (right-eq right-index)) eq))
    ; target-blame-reflects =
        λ eq →
          let m , U , source-eq =
                target-blame-reflects simulation
                  (trans (sym (right-eq right-index)) eq)
          in m , U , trans (left-eq m) source-eq
    }

indexed-typed-result :
  ∀ {W W′ A B left-index right-index}
    {R : WorldRelation W W′}
    {left right : Computation} →
  IndexedTerminalSimulation ValueNarrowing R left right
    left-index right-index →
  (∀ n → OutcomeTyping W A (left n)) →
  (∀ n → OutcomeTyping W′ B (right n)) →
  IndexedTerminalSimulation (TypedValueResult A B) R left right
    left-index right-index
indexed-typed-result
    {left-index = left-index} {right-index}
    simulation left-typing right-typing =
  record
    { forward-return =
        λ eq →
          let m , U′ , V′ , S , R≤S , right-eq , V~V′ =
                forward-return simulation eq
          in m , U′ , V′ , S , R≤S , right-eq ,
             typed-value-narrowing V~V′
               (returned-world (left-typing left-index) eq)
               (returned-world (right-typing m) right-eq)
               (returned-value (left-typing left-index) eq)
               (returned-value (right-typing m) right-eq)
    ; backward-return =
        λ eq →
          Data.Sum.map
            (λ
              { (m , U , V , S , R≤S , left-eq , V~V′) →
                  m , U , V , S , R≤S , left-eq ,
                  typed-value-narrowing V~V′
                    (returned-world (left-typing m) left-eq)
                    (returned-world
                      (right-typing right-index) eq)
                    (returned-value (left-typing m) left-eq)
                    (returned-value
                      (right-typing right-index) eq)
              })
            (λ blame → blame)
            (backward-return simulation eq)
    ; target-blame-reflects =
        target-blame-reflects simulation
    }
  where
  returned-world :
    ∀ {Z U V C o} →
    OutcomeTyping Z C o →
    o ≡ returned U V →
    Typing.InterpreterSemanticTypingCore.WorldTyping U
  returned-world typed eq
      with subst (OutcomeTyping _ _) eq typed
  returned-world typed eq
      | return-typed Z≤U U⊢ V⊢ =
    U⊢

  returned-value :
    ∀ {Z U V C o} →
    OutcomeTyping Z C o →
    o ≡ returned U V →
    Typing.InterpreterSemanticTypingCore.ValueTyping U V C
  returned-value typed eq
      with subst (OutcomeTyping _ _) eq typed
  returned-value typed eq
      | return-typed Z≤U U⊢ V⊢ =
    V⊢
