module proof.InterpreterSequenceSimulation where

-- File Charter:
--   * Lifts terminal simulation through one interpreter sequencing point.
--   * Joins independently delayed head and continuation observations by fuel
--     addition and terminal stability.
--   * Uses only interpreter equations and world/value narrowing.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import Interpreter
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterTermNarrowing as ITN
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import proof.InterpreterSimulationHelpers

open ITN.InterpreterValues
open ITN.RelatedWorlds
open import proof.InterpreterGuardSimulation using (unguard-simulation)

module SequenceWorldProof =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

sequence-backward-return :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  ∀ {n Z′ Q′} →
  sequence W′ right-head right-continuation n ≡ returned Z′ Q′ →
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
sequence-backward-return head-simulation continuation-simulation
    {n = zero} ()
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    with right-head n in head-eq
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | timed U′ =
  ⊥-elim (timed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | blamed U′ =
  ⊥-elim (blamed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | failed U′ e =
  ⊥-elim (failed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′
    with right-continuation U′ V′ n in continuation-eq
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | blamed Z′ =
  ⊥-elim (blamed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (failed≢returned result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | returned Z′ Q′
    with backward-return head-simulation head-eq
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
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
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with backward-return
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₂ (q , Z , left-continuation-blame) =
  inj₂
    ( suc (m + q)
    , Z
    , sequence-continuation-terminal
        {W = W}
        {head = left-head}
        {continuation = left-continuation}
        {m = m} {q = q} {U = U} {V = V}
        (left-stable head-simulation)
        (left-stable (continuation-simulation R≤S V~V′))
        left-head-eq terminal-blame left-continuation-blame
    )
sequence-backward-return
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | returned Z′ Q′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | inj₁
        (q , Z , Q , T , S≤T , left-continuation-eq , Q~Q′) =
  inj₁
    ( suc (m + q)
    , Z
    , Q
    , T
    , SequenceWorldProof.world-extension-trans R≤S S≤T
    , sequence-continuation-terminal
        {W = W}
        {head = left-head}
        {continuation = left-continuation}
        {m = m} {q = q} {U = U} {V = V}
        (left-stable head-simulation)
        (left-stable (continuation-simulation R≤S V~V′))
        left-head-eq terminal-return left-continuation-eq
    , Q~Q′
    )

sequence-target-blame :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  ∀ {n Z′} →
  sequence W′ right-head right-continuation n ≡ blamed Z′ →
  Σ[ m ∈ StepIndex ]
  Σ[ Z ∈ World ]
    sequence W left-head left-continuation m ≡ blamed Z
sequence-target-blame head-simulation continuation-simulation
    {n = zero} ()
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    with right-head n in head-eq
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | timed U′ =
  ⊥-elim (timed≢blamed result-eq)
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | blamed U′
    with target-blame-reflects head-simulation head-eq
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | blamed U′ | m , U , left-head-blame =
  suc m , U ,
  sequence-head-blame
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {U = U}
    left-head-blame
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | failed U′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′
    with right-continuation U′ V′ n in continuation-eq
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | timed Z′ =
  ⊥-elim (timed≢blamed result-eq)
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | blamed Z′
    with backward-return head-simulation head-eq
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | blamed Z′
    | inj₂ (m , U , left-head-blame) =
  suc m , U ,
  sequence-head-blame
    {W = W} {head = left-head}
    {continuation = left-continuation}
    {m = m} {U = U}
    left-head-blame
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    with target-blame-reflects
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | blamed Z′
    | inj₁ (m , U , V , S , R≤S , left-head-eq , V~V′)
    | q , Z , left-continuation-blame =
  suc (m + q) , Z ,
  sequence-continuation-terminal
    {W = W}
    {head = left-head}
    {continuation = left-continuation}
    {m = m} {q = q} {U = U} {V = V}
    (left-stable head-simulation)
    (left-stable (continuation-simulation R≤S V~V′))
    left-head-eq terminal-blame left-continuation-blame
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | failed Z′ e =
  ⊥-elim (blamed≢failed (sym result-eq))
sequence-target-blame
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U′ V′ | returned Z′ Q′ =
  ⊥-elim (blamed≢returned (sym result-eq))

sequence-left-error-impossible :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  ∀ {n Z e} →
  sequence W left-head left-continuation n ≡ failed Z e →
  ⊥
sequence-left-error-impossible head-simulation continuation-simulation
    {n = zero} ()
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    with left-head n in head-eq
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | timed U =
  ⊥-elim (timed≢failed result-eq)
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | blamed U =
  ⊥-elim (blamed≢failed result-eq)
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | failed U e =
  left-error-impossible head-simulation head-eq
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V
    with forward-return head-simulation head-eq
sequence-left-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′ =
  left-error-impossible
    (continuation-simulation R≤S V~V′)
    result-eq

sequence-right-error-impossible :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  TerminalSimulation head-result R left-head right-head →
  (∀ U′ V′ {n Z′ e} →
    right-continuation U′ V′ n ≡ failed Z′ e →
    ⊥) →
  ∀ {n Z′ e} →
  sequence W′ right-head right-continuation n ≡ failed Z′ e →
  ⊥
sequence-right-error-impossible head-simulation right-error-free
    {n = zero} ()
sequence-right-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation right-error-free
    {n = suc n} result-eq
    with right-head n in head-eq
sequence-right-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation right-error-free
    {n = suc n} result-eq
    | timed U′ =
  ⊥-elim (timed≢failed result-eq)
sequence-right-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation right-error-free
    {n = suc n} result-eq
    | blamed U′ =
  ⊥-elim (blamed≢failed result-eq)
sequence-right-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation right-error-free
    {n = suc n} result-eq
    | failed U′ e =
  right-error-impossible head-simulation head-eq
sequence-right-error-impossible
    {W} {W′} {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation right-error-free
    {n = suc n} result-eq
    | returned U′ V′ =
  right-error-free U′ V′ result-eq

sequence-simulation :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (continuation-simulation :
    ∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  (∀ {n Z′ e} →
    sequence W′ right-head right-continuation n ≡ failed Z′ e →
    ⊥) →
  TerminalSimulation continuation-result R
    (sequence W left-head left-continuation)
    (sequence W′ right-head right-continuation)
sequence-simulation
    {W} {W′} {head-result} {continuation-result}
    {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-continuation-stable right-continuation-stable
    right-sequence-error-free =
  record
    { left-stable =
        λ { {n} {o} terminal eq k →
          sequence-terminal-stable
            {W = W}
            {head = left-head}
            {continuation = left-continuation}
            (left-stable head-simulation)
            left-continuation-stable
            {n = n} {o = o} terminal eq k
          }
    ; right-stable =
        λ { {n} {o} terminal eq k →
          sequence-terminal-stable
            {W = W′}
            {head = right-head}
            {continuation = right-continuation}
            (right-stable head-simulation)
            right-continuation-stable
            {n = n} {o = o} terminal eq k
          }
    ; forward-return =
        λ { {n} {U} {V} eq →
          sequence-forward-return
            {W = W} {W′ = W′} {R = R}
            {left-head = left-head} {right-head = right-head}
            {left-continuation = left-continuation}
            {right-continuation = right-continuation}
            head-simulation continuation-simulation
            {n = n} {Z = U} {Q = V} eq
          }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          sequence-backward-return
            {W = W} {W′ = W′} {R = R}
            {left-head = left-head} {right-head = right-head}
            {left-continuation = left-continuation}
            {right-continuation = right-continuation}
            head-simulation continuation-simulation
            {n = n} {Z′ = U′} {Q′ = V′} eq
          }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          sequence-target-blame
            {W = W} {W′ = W′} {R = R}
            {left-head = left-head} {right-head = right-head}
            {left-continuation = left-continuation}
            {right-continuation = right-continuation}
            head-simulation continuation-simulation
            {n = n} {Z′ = U′} eq
          }
    ; left-error-impossible =
        λ { {n} {U} {e} eq →
          sequence-left-error-impossible
            {W = W} {W′ = W′} {R = R}
            {left-head = left-head} {right-head = right-head}
            {left-continuation = left-continuation}
            {right-continuation = right-continuation}
            head-simulation continuation-simulation
            {n = n} {Z = U} {e = e} eq
          }
    ; right-error-impossible =
        λ { {n} {U′} {e} eq →
          right-sequence-error-free
            {n = n} {Z′ = U′} {e = e} eq
          }
    }

chain-simulation :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation right-continuation :
      World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (continuation-simulation :
    ∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  (∀ U V → TerminalStable (left-continuation U V)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  (∀ {n Z′ e} →
    chain right-head right-continuation n ≡ failed Z′ e →
    ⊥) →
  TerminalSimulation continuation-result R
    (chain left-head left-continuation)
    (chain right-head right-continuation)
chain-simulation
    {W} {W′} {head-result} {continuation-result}
    {R = R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    left-continuation-stable right-continuation-stable
    right-chain-error-free =
  unguard-simulation
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = left-head} {right-head = right-head}
      {left-continuation = left-continuation}
      {right-continuation = right-continuation}
      head-simulation continuation-simulation
      left-continuation-stable right-continuation-stable
      (λ { {zero} ()
         ; {suc n} eq → right-chain-error-free eq
         }))
