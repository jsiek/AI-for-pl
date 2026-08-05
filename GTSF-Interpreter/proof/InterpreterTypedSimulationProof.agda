module proof.InterpreterTypedSimulationProof where

-- File Charter:
--   * Upgrades terminal simulation from value narrowing to typed value
--     narrowing using independent unary outcome-typing proofs.
--   * Extracts returned-value typing constructively from outcome equations.
--   * Contains no interpreter recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)

open import Interpreter
open import Typing.InterpreterSemanticTypingCore using
  ( OutcomeTyping
  ; SemanticType
  ; ValueTyping
  ; WorldTyping
  ; return-typed
  )
open import Simulation.Core.InterpreterSimulationResult
open import Narrowing.InterpreterTypedValueNarrowing
import Narrowing.InterpreterTermNarrowing as ITN

open ITN.InterpreterValues
open ITN.RelatedWorlds

returned-value-typing :
  ∀ {W U V A o} →
  OutcomeTyping W A o →
  o ≡ returned U V →
  ValueTyping U V A
returned-value-typing typed eq
    with subst (OutcomeTyping _ _) eq typed
returned-value-typing typed eq
    | return-typed W≤U U⊢ V⊢ =
  V⊢

returned-world-typing :
  ∀ {W U V A o} →
  OutcomeTyping W A o →
  o ≡ returned U V →
  WorldTyping U
returned-world-typing typed eq
    with subst (OutcomeTyping _ _) eq typed
returned-world-typing typed eq
    | return-typed W≤U U⊢ V⊢ =
  U⊢

typed-forward-return :
  ∀ {W W′ A B}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  (∀ n → OutcomeTyping W A (left n)) →
  (∀ n → OutcomeTyping W′ B (right n)) →
  ∀ {n U V} →
  left n ≡ returned U V →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U′ →
          Data.Product.Σ Value
            (λ V′ →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  right m ≡ returned U′ V′ ×
                  TypedValueNarrowing A B S V V′))))
typed-forward-return simulation left-typing right-typing
    {n} returned-eq
    with forward-return simulation returned-eq
typed-forward-return simulation left-typing right-typing
    {n} returned-eq
    | m , U′ , V′ , S , R≤S , right-eq , V~V′ =
  m , U′ , V′ , S , R≤S , right-eq ,
  typed-value-narrowing V~V′
    (returned-world-typing (left-typing n) returned-eq)
    (returned-world-typing (right-typing m) right-eq)
    (returned-value-typing (left-typing n) returned-eq)
    (returned-value-typing (right-typing m) right-eq)

typed-backward-return :
  ∀ {W W′ A B}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  (∀ n → OutcomeTyping W A (left n)) →
  (∀ n → OutcomeTyping W′ B (right n)) →
  ∀ {n U′ V′} →
  right n ≡ returned U′ V′ →
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U →
          Data.Product.Σ Value
            (λ V →
              Data.Product.Σ (WorldRelation U U′)
                (λ S →
                  WorldExtension R S ×
                  left m ≡ returned U V ×
                  TypedValueNarrowing A B S V V′)))))
  ⊎
  (Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ U → left m ≡ blamed U)))
typed-backward-return simulation left-typing right-typing
    {n} returned-eq
    with backward-return simulation returned-eq
typed-backward-return simulation left-typing right-typing
    {n} returned-eq
    | inj₂ blame-result =
  inj₂ blame-result
typed-backward-return simulation left-typing right-typing
    {n} returned-eq
    | inj₁ (m , U , V , S , R≤S , left-eq , V~V′) =
  inj₁
    ( m , U , V , S , R≤S , left-eq
    , typed-value-narrowing V~V′
        (returned-world-typing (left-typing m) left-eq)
        (returned-world-typing (right-typing n) returned-eq)
        (returned-value-typing (left-typing m) left-eq)
        (returned-value-typing (right-typing n) returned-eq)
    )

typed-result-simulation :
  ∀ {W W′ A B}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation ValueNarrowing R left right →
  (∀ n → OutcomeTyping W A (left n)) →
  (∀ n → OutcomeTyping W′ B (right n)) →
  TerminalSimulation (TypedValueResult A B) R left right
typed-result-simulation simulation left-typing right-typing =
  record
    { left-stable = left-stable simulation
    ; right-stable = right-stable simulation
    ; forward-return =
        typed-forward-return simulation left-typing right-typing
    ; backward-return =
        typed-backward-return simulation left-typing right-typing
    ; target-blame-reflects =
        target-blame-reflects simulation
    ; left-error-impossible =
        left-error-impossible simulation
    ; right-error-impossible =
        right-error-impossible simulation
    }
