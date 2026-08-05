module proof.InterpreterIndexedSequenceSimulation where

-- File Charter:
--   * Composes fuel-local simulations through one interpreter sequence.
--   * Uses simulations only at the predecessor of the observed sequence
--     index, making the decrease visible to Agda's termination checker.
--   * Joins independently delayed matching executions by terminal stability.
--   * Contains no evaluator recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (suc; _+_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Simulation.Indexed.InterpreterIndexedSimulation
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterTermNarrowing as ITN
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import proof.InterpreterSimulationHelpers using
  (sequence-continuation-terminal; sequence-head-blame)

open ITN.InterpreterValues
open ITN.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

indexed-sequence-forward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index right-index) →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  ∀ {Z Q} →
  sequence W left-head left-continuation (suc left-index) ≡
    returned Z Q →
  Σ[ m ∈ StepIndex ]
  Σ[ Z′ ∈ World ]
  Σ[ Q′ ∈ Value ]
  Σ[ T ∈ WorldRelation Z Z′ ]
    WorldExtension R T ×
    sequence W′ right-head right-continuation m ≡ returned Z′ Q′ ×
    continuation-result T Q Q′
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    with left-head left-index in head-eq
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | timed U =
  ⊥-elim (timed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | blamed U =
  ⊥-elim (blamed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | failed U e =
  ⊥-elim (failed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V
    with left-continuation U V left-index in continuation-eq
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | timed Z =
  ⊥-elim (timed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | blamed Z =
  ⊥-elim (blamed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | failed Z e =
  ⊥-elim (failed≢returned result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | returned Z Q
    with forward-return head-simulation head-eq
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    with forward-return
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
indexed-sequence-forward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    right-head-stable right-continuation-stable result-eq
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    | q , Z′ , Q′ , T , S≤T , right-continuation-eq , Q~Q′ =
  suc (m + q) , Z′ , Q′ , T ,
  WorldProof.world-extension-trans R≤S S≤T ,
  sequence-continuation-terminal
    {W = W′} {head = right-head}
    {continuation = right-continuation}
    {m = m} {q = q} {U = U′} {V = V′}
    right-head-stable
    (right-continuation-stable U′ V′)
    right-head-eq terminal-return right-continuation-eq ,
  Q~Q′

indexed-sequence-backward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index right-index) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  ∀ {Z′ Q′} →
  sequence W′ right-head right-continuation (suc right-index) ≡
    returned Z′ Q′ →
  (Σ[ m ∈ StepIndex ]
   Σ[ Z ∈ World ]
   Σ[ Q ∈ Value ]
   Σ[ T ∈ WorldRelation Z Z′ ]
     WorldExtension R T ×
     sequence W left-head left-continuation m ≡ returned Z Q ×
     continuation-result T Q Q′)
  ⊎
  (Σ[ m ∈ StepIndex ]
   Σ[ Z ∈ World ]
     sequence W left-head left-continuation m ≡ blamed Z)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    with right-head right-index in head-eq
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | timed U′ =
  ⊥-elim (timed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | blamed U′ =
  ⊥-elim (blamed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | failed U′ e =
  ⊥-elim (failed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′
    with right-continuation U′ V′ right-index in continuation-eq
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | blamed Z′ =
  ⊥-elim (blamed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (failed≢returned result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′
    with backward-return head-simulation head-eq
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₂ (m , U , left-head-blame) =
  inj₂
    ( suc m
    , U
    , sequence-head-blame
        {W = W} {head = left-head}
        {continuation = left-continuation}
        {m = m} {U = U}
        left-head-blame
    )
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with backward-return
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₂ (q , Z , left-continuation-blame) =
  inj₂
    ( suc (m + q)
    , Z
    , sequence-continuation-terminal
        {W = W} {head = left-head}
        {continuation = left-continuation}
        {m = m} {q = q} {U = U} {V = V}
        left-head-stable
        (left-continuation-stable U V)
        left-head-eq terminal-blame left-continuation-blame
    )
indexed-sequence-backward
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₁
        (q , Z , Q , T , S≤T , left-continuation-eq , Q~Q′) =
  inj₁
    ( suc (m + q)
    , Z
    , Q
    , T
    , WorldProof.world-extension-trans R≤S S≤T
    , sequence-continuation-terminal
        {W = W} {head = left-head}
        {continuation = left-continuation}
        {m = m} {q = q} {U = U} {V = V}
        left-head-stable
        (left-continuation-stable U V)
        left-head-eq terminal-return left-continuation-eq
    , Q~Q′
    )

indexed-sequence-target-blame :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index right-index) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  ∀ {Z′} →
  sequence W′ right-head right-continuation (suc right-index) ≡
    blamed Z′ →
  Σ[ m ∈ StepIndex ]
  Σ[ Z ∈ World ]
    sequence W left-head left-continuation m ≡ blamed Z
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    with right-head right-index in head-eq
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | timed U′ =
  ⊥-elim (timed≢blamed result-eq)
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | blamed U′
    with target-blame-reflects head-simulation head-eq
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | blamed U′ | m , U , left-head-blame =
  suc m , U ,
  sequence-head-blame
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {U = U}
    left-head-blame
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | failed U′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′
    with right-continuation U′ V′ right-index in continuation-eq
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢blamed result-eq)
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | blamed Z′
    with backward-return head-simulation head-eq
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | blamed Z′
    | inj₂ (m , U , left-head-blame) =
  suc m , U ,
  sequence-head-blame
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {U = U}
    left-head-blame
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with target-blame-reflects
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | q , Z , left-continuation-blame =
  suc (m + q) , Z ,
  sequence-continuation-terminal
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {q = q} {U = U} {V = V}
    left-head-stable
    (left-continuation-stable U V)
    left-head-eq terminal-blame left-continuation-blame
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
indexed-sequence-target-blame
    {W} {W′} {left-index} {right-index} {R = R}
    {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable result-eq
    | returned U′ V′ | returned Z′ Q′ =
  ⊥-elim (blamed≢returned (sym result-eq))

indexed-sequence-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′) left-index right-index) →
  TerminalStable left-head →
  TerminalStable right-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  IndexedTerminalSimulation continuation-result R
    (sequence W left-head left-continuation)
    (sequence W′ right-head right-continuation)
    (suc left-index)
    (suc right-index)
indexed-sequence-simulation
    head-simulation continuation-simulation
    left-head-stable right-head-stable
    left-continuation-stable right-continuation-stable =
  record
    { forward-return =
        indexed-sequence-forward
          head-simulation continuation-simulation
          right-head-stable right-continuation-stable
    ; backward-return =
        indexed-sequence-backward
          head-simulation continuation-simulation
          left-head-stable left-continuation-stable
    ; target-blame-reflects =
        indexed-sequence-target-blame
          head-simulation continuation-simulation
          left-head-stable left-continuation-stable
    }
