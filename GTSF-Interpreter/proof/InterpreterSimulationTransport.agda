module proof.InterpreterSimulationTransport where

-- File Charter:
--   * Transports terminal simulation across pointwise computation equations.
--   * Avoids function extensionality when unfolding interpreter equations.
--   * Contains no syntax, typing, or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
import Data.Nat
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter using (StepIndex)
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.RelatedWorlds

transport-forward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (left-eq : ∀ n → left n ≡ left′ n) →
  (right-eq : ∀ n → right n ≡ right′ n) →
  TerminalSimulation value-result R left′ right′ →
  ∀ {n U V} →
  left n ≡ Interpreter.returned U V →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ Interpreter.World
        (λ U′ →
          Data.Product.Σ Interpreter.Value
            (λ V′ →
              Data.Product.Σ
                (ITN.RelatedWorlds.WorldRelation U U′)
                (λ S →
                  ITN.RelatedWorlds.WorldExtension R S ×
                  right m ≡ Interpreter.returned U′ V′ ×
                  value-result S V V′))))
transport-forward-return left-eq right-eq simulation {n} eq
    with forward-return simulation
      (trans (sym (left-eq n)) eq)
transport-forward-return left-eq right-eq simulation eq
    | m , U′ , V′ , S , R≤S , returned-eq , V~V′ =
  m , U′ , V′ , S , R≤S ,
  trans (right-eq m) returned-eq , V~V′

transport-backward-return :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (left-eq : ∀ n → left n ≡ left′ n) →
  (right-eq : ∀ n → right n ≡ right′ n) →
  TerminalSimulation value-result R left′ right′ →
  ∀ {n U′ V′} →
  right n ≡ Interpreter.returned U′ V′ →
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ Interpreter.World
        (λ U →
          Data.Product.Σ Interpreter.Value
            (λ V →
              Data.Product.Σ
                (ITN.RelatedWorlds.WorldRelation U U′)
                (λ S →
                  ITN.RelatedWorlds.WorldExtension R S ×
                  left m ≡ Interpreter.returned U V ×
                  value-result S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ Interpreter.World
        (λ U → left m ≡ Interpreter.blamed U)))
transport-backward-return left-eq right-eq simulation {n} eq
    with backward-return simulation
      (trans (sym (right-eq n)) eq)
transport-backward-return left-eq right-eq simulation eq
    | inj₁ (m , U , V , S , R≤S , returned-eq , V~V′) =
  inj₁
    ( m , U , V , S , R≤S ,
      trans (left-eq m) returned-eq , V~V′
    )
transport-backward-return left-eq right-eq simulation eq
    | inj₂ (m , U , blame-eq) =
  inj₂ (m , U , trans (left-eq m) blame-eq)

transport-target-blame :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (left-eq : ∀ n → left n ≡ left′ n) →
  (right-eq : ∀ n → right n ≡ right′ n) →
  TerminalSimulation value-result R left′ right′ →
  ∀ {n U′} →
  right n ≡ Interpreter.blamed U′ →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ Interpreter.World
        (λ U → left m ≡ Interpreter.blamed U))
transport-target-blame left-eq right-eq simulation {n} eq
    with target-blame-reflects simulation
      (trans (sym (right-eq n)) eq)
transport-target-blame left-eq right-eq simulation eq
    | m , U , blame-eq =
  m , U , trans (left-eq m) blame-eq

simulation-pointwise :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left left′ right right′ : Computation} →
  (∀ n → left n ≡ left′ n) →
  (∀ n → right n ≡ right′ n) →
  TerminalSimulation value-result R left′ right′ →
  TerminalSimulation value-result R left right
simulation-pointwise left-eq right-eq simulation =
  record
    { left-stable =
        λ { {n} {o} terminal eq k →
          trans
            (left-eq (n Data.Nat.+ k))
            (left-stable simulation terminal
              (trans (sym (left-eq n)) eq) k)
          }
    ; right-stable =
        λ { {n} {o} terminal eq k →
          trans
            (right-eq (n Data.Nat.+ k))
            (right-stable simulation terminal
              (trans (sym (right-eq n)) eq) k)
          }
    ; forward-return =
        transport-forward-return left-eq right-eq simulation
    ; backward-return =
        transport-backward-return left-eq right-eq simulation
    ; target-blame-reflects =
        transport-target-blame left-eq right-eq simulation
    ; left-error-impossible =
        λ { {n} eq →
          left-error-impossible simulation
            (trans (sym (left-eq n)) eq)
          }
    ; right-error-impossible =
        λ { {n} eq →
          right-error-impossible simulation
            (trans (sym (right-eq n)) eq)
          }
    }
