module proof.InterpreterIndexedOneSidedSequenceSimulation where

-- File Charter:
--   * Lifts fuel-local simulation through a continuation on the left only.
--   * Keeps the target endpoint at its original observation index.
--   * Uses the target computation's zero-index equation to discharge the
--     otherwise impossible zero-index backward-return branch.
--   * Contains no evaluator recursion or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc; _+_)
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
open import proof.InterpreterIndexedGuardRemoval using
  (remove-left-guard)

open ITN.InterpreterValues
open ITN.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

indexed-left-sequence-forward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) left-index right-index) →
  ∀ {Z Q} →
  sequence W left-head left-continuation (suc left-index) ≡
    returned Z Q →
  Σ[ m ∈ StepIndex ]
  Σ[ Z′ ∈ World ]
  Σ[ Q′ ∈ Value ]
  Σ[ T ∈ WorldRelation Z Z′ ]
    WorldExtension R T ×
    right-head m ≡ returned Z′ Q′ ×
    continuation-result T Q Q′
indexed-left-sequence-forward
    {left-index = left-index} {R = R}
    {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation result-eq
    with left-head left-index in head-eq
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | timed U =
  ⊥-elim (timed≢returned result-eq)
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | blamed U =
  ⊥-elim (blamed≢returned result-eq)
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | failed U e =
  ⊥-elim (failed≢returned result-eq)
indexed-left-sequence-forward
    {left-index = left-index} {R = R}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation result-eq
    | returned U V
    with left-continuation U V left-index in continuation-eq
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | returned U V | timed Z =
  ⊥-elim (timed≢returned result-eq)
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | returned U V | blamed Z =
  ⊥-elim (blamed≢returned result-eq)
indexed-left-sequence-forward
    head-simulation continuation-simulation result-eq
    | returned U V | failed Z e =
  ⊥-elim (failed≢returned result-eq)
indexed-left-sequence-forward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U V | returned Z Q
    with forward-return head-simulation head-eq
indexed-left-sequence-forward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    with forward-return
      (continuation-simulation R≤S V~V′)
      continuation-eq
indexed-left-sequence-forward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    | zero , Z′ , Q′ , T , S≤T , () , Q~Q′
indexed-left-sequence-forward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    | suc q , .U′ , .V′ , T , S≤T , refl , Q~Q′ =
  m , U′ , V′ , T ,
  WorldProof.world-extension-trans R≤S S≤T ,
  right-head-eq ,
  Q~Q′

indexed-left-sequence-backward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) left-index right-index) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  right-head zero ≡ timed W′ →
  ∀ {Z′ Q′} →
  right-head right-index ≡ returned Z′ Q′ →
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
indexed-left-sequence-backward
    {right-index = zero}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq =
  ⊥-elim (timed≢returned (trans (sym right-zero) result-eq))
indexed-left-sequence-backward
    {W = W} {left-index = left-index}
    {right-index = suc right-index} {R = R}
    {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq
    with backward-return head-simulation result-eq
indexed-left-sequence-backward
    {W = W} {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq
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
indexed-left-sequence-backward
    {W = W} {left-index = left-index}
    {right-index = suc right-index} {R = R}
    {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with backward-return
      (continuation-simulation R≤S V~V′)
      {U′ = _} {V′ = _} refl
indexed-left-sequence-backward
    {W = W} {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq
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
indexed-left-sequence-backward
    {W = W} {R = R}
    {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable
    right-zero result-eq
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

indexed-left-sequence-target-blame :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  TerminalStable left-head →
  ∀ {Z′} →
  right-head right-index ≡ blamed Z′ →
  Σ[ m ∈ StepIndex ]
  Σ[ Z ∈ World ]
    sequence W left-head left-continuation m ≡ blamed Z
indexed-left-sequence-target-blame
    {W = W} {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation left-head-stable result-eq
    with target-blame-reflects head-simulation result-eq
indexed-left-sequence-target-blame
    {W = W} {left-head = left-head}
    {left-continuation = left-continuation}
    head-simulation left-head-stable result-eq
    | m , U , left-head-blame =
  suc m , U ,
  sequence-head-blame
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {U = U}
    left-head-blame

indexed-left-sequence-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) left-index right-index) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  right-head zero ≡ timed W′ →
  IndexedTerminalSimulation continuation-result R
    (sequence W left-head left-continuation)
    right-head (suc left-index) right-index
indexed-left-sequence-simulation
    {continuation-result = continuation-result}
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable right-zero =
  record
    { forward-return =
        indexed-left-sequence-forward
          head-simulation continuation-simulation
    ; backward-return =
        indexed-left-sequence-backward
          head-simulation continuation-simulation
          left-head-stable left-continuation-stable right-zero
    ; target-blame-reflects =
        indexed-left-sequence-target-blame
          {continuation-result = continuation-result}
          head-simulation left-head-stable
    }

indexed-left-chain-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′) left-index right-index) →
  TerminalStable left-head →
  (∀ U V → TerminalStable (left-continuation U V)) →
  right-head zero ≡ timed W′ →
  IndexedTerminalSimulation continuation-result R
    (chain left-head left-continuation)
    right-head left-index right-index
indexed-left-chain-simulation
    head-simulation continuation-simulation
    left-head-stable left-continuation-stable right-zero =
  remove-left-guard
    (indexed-left-sequence-simulation
      head-simulation continuation-simulation
      left-head-stable left-continuation-stable right-zero)
