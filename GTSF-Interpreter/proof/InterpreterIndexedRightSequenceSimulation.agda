module proof.InterpreterIndexedRightSequenceSimulation where

-- File Charter:
--   * Lifts fuel-local simulation through a continuation on the right only.
--   * Keeps the source endpoint at its original observation index.
--   * Uses the source computation's zero-index equation for the impossible
--     zero-index forward branch.
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
open import proof.InterpreterIndexedGuardRemoval using
  (remove-right-guard)
open import proof.InterpreterSimulationHelpers using
  (sequence-continuation-terminal; sequence-head-blame)

open ITN.InterpreterValues
open ITN.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

indexed-right-sequence-forward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index right-index) →
  left-head zero ≡ timed W →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  ∀ {Z Q} →
  left-head left-index ≡ returned Z Q →
  Σ[ m ∈ StepIndex ]
  Σ[ Z′ ∈ World ]
  Σ[ Q′ ∈ Value ]
  Σ[ T ∈ WorldRelation Z Z′ ]
    WorldExtension R T ×
    sequence W′ right-head right-continuation m ≡ returned Z′ Q′ ×
    continuation-result T Q Q′
indexed-right-sequence-forward
    {left-index = zero}
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable result-eq =
  ⊥-elim (timed≢returned (trans (sym left-zero) result-eq))
indexed-right-sequence-forward
    {W′ = W′} {left-index = suc left-index}
    {R = R} {right-head = right-head}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable result-eq
    with forward-return head-simulation result-eq
indexed-right-sequence-forward
    {W′ = W′} {left-index = suc left-index}
    {R = R} {right-head = right-head}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable result-eq
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    with forward-return
      (continuation-simulation R≤S V~V′)
      {U = _} {V = _} refl
indexed-right-sequence-forward
    {W′ = W′} {R = R}
    {right-head = right-head}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable result-eq
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

indexed-right-sequence-backward :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index right-index) →
  ∀ {Z′ Q′} →
  sequence W′ right-head right-continuation (suc right-index) ≡
    returned Z′ Q′ →
  (Σ[ m ∈ StepIndex ]
   Σ[ Z ∈ World ]
   Σ[ Q ∈ Value ]
   Σ[ T ∈ WorldRelation Z Z′ ]
     WorldExtension R T ×
     left-head m ≡ returned Z Q ×
     continuation-result T Q Q′)
  ⊎
  (Σ[ m ∈ StepIndex ]
   Σ[ Z ∈ World ]
     left-head m ≡ blamed Z)
indexed-right-sequence-backward
    {right-index = right-index}
    {right-head = right-head}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation result-eq
    with right-head right-index in head-eq
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | timed U′ =
  ⊥-elim (timed≢returned result-eq)
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | blamed U′ =
  ⊥-elim (blamed≢returned result-eq)
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | failed U′ e =
  ⊥-elim (failed≢returned result-eq)
indexed-right-sequence-backward
    {right-index = right-index}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation result-eq
    | returned U′ V′
    with right-continuation U′ V′ right-index in continuation-eq
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢returned result-eq)
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | blamed Z′ =
  ⊥-elim (blamed≢returned result-eq)
indexed-right-sequence-backward
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (failed≢returned result-eq)
indexed-right-sequence-backward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    with backward-return head-simulation head-eq
indexed-right-sequence-backward
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₂ (m , U , left-head-blame) =
  inj₂ (m , U , left-head-blame)
indexed-right-sequence-backward
    {left-index = left-index} {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with backward-return
      (continuation-simulation R≤S V~V′)
      continuation-eq
indexed-right-sequence-backward
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₂ (zero , Z , ())
indexed-right-sequence-backward
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₂ (suc q , Z , ())
indexed-right-sequence-backward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₁
        (zero , Z , Q , T , S≤T , () , Q~Q′)
indexed-right-sequence-backward
    {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₁
        (suc q , .U , .V , T , S≤T , refl , Q~Q′) =
  inj₁
    ( m
    , U
    , V
    , T
    , WorldProof.world-extension-trans R≤S S≤T
    , left-head-eq
    , Q~Q′
    )

indexed-right-sequence-target-blame :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index right-index) →
  ∀ {Z′} →
  sequence W′ right-head right-continuation (suc right-index) ≡
    blamed Z′ →
  Σ[ m ∈ StepIndex ]
  Σ[ Z ∈ World ]
    left-head m ≡ blamed Z
indexed-right-sequence-target-blame
    {right-index = right-index}
    {right-head = right-head}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation result-eq
    with right-head right-index in head-eq
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | timed U′ =
  ⊥-elim (timed≢blamed result-eq)
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | blamed U′ =
  target-blame-reflects head-simulation head-eq
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | failed U′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
indexed-right-sequence-target-blame
    {right-index = right-index}
    {right-continuation = right-continuation}
    head-simulation continuation-simulation result-eq
    | returned U′ V′
    with right-continuation U′ V′ right-index in continuation-eq
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢blamed result-eq)
indexed-right-sequence-target-blame
    {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | blamed Z′
    with backward-return head-simulation head-eq
indexed-right-sequence-target-blame
    head-simulation continuation-simulation refl
    | returned U′ V′ | blamed Z′
    | inj₂ (m , U , left-head-blame) =
  m , U , left-head-blame
indexed-right-sequence-target-blame
    {left-index = left-index} {R = R}
    head-simulation continuation-simulation refl
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with target-blame-reflects
      (continuation-simulation R≤S V~V′)
      continuation-eq
indexed-right-sequence-target-blame
    head-simulation continuation-simulation refl
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | zero , Z , ()
indexed-right-sequence-target-blame
    head-simulation continuation-simulation refl
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | suc q , Z , ()
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
indexed-right-sequence-target-blame
    head-simulation continuation-simulation result-eq
    | returned U′ V′ | returned Z′ Q′ =
  ⊥-elim (blamed≢returned (sym result-eq))

indexed-right-sequence-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index right-index) →
  left-head zero ≡ timed W →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  IndexedTerminalSimulation continuation-result R
    left-head
    (sequence W′ right-head right-continuation)
    left-index (suc right-index)
indexed-right-sequence-simulation
    {continuation-result = continuation-result}
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable =
  record
    { forward-return =
        indexed-right-sequence-forward
          head-simulation continuation-simulation left-zero
          right-head-stable right-continuation-stable
    ; backward-return =
        indexed-right-sequence-backward
          head-simulation continuation-simulation
    ; target-blame-reflects =
        indexed-right-sequence-target-blame
          {continuation-result = continuation-result}
          head-simulation continuation-simulation
    }

indexed-right-chain-simulation :
  ∀ {W W′ left-index right-index}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  IndexedTerminalSimulation
    head-result R left-head right-head left-index right-index →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    IndexedTerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′) left-index right-index) →
  left-head zero ≡ timed W →
  TerminalStable right-head →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  IndexedTerminalSimulation continuation-result R
    left-head
    (chain right-head right-continuation)
    left-index right-index
indexed-right-chain-simulation
    head-simulation continuation-simulation left-zero
    right-head-stable right-continuation-stable =
  remove-right-guard
    (indexed-right-sequence-simulation
      head-simulation continuation-simulation left-zero
      right-head-stable right-continuation-stable)
