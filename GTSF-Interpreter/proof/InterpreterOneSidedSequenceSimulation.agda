module proof.InterpreterOneSidedSequenceSimulation where

-- File Charter:
--   * Lifts terminal simulation through a continuation on either side only.
--   * Removes sequencing with `immediateReturn` from either endpoint.
--   * Uses only computation equations and terminal stability.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import Interpreter
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterTermNarrowing as ITN
open import proof.InterpreterSequenceSimulation using
  (sequence-right-error-impossible; sequence-simulation)
open import proof.InterpreterSimulationHelpers using
  ( immediate-return-terminal-stable
  ; sequence-after-return
  ; sequence-head-blame
  ; sequence-head-error
  ; terminal-stable-at-right-sum
  )

open ITN.InterpreterValues
open ITN.RelatedWorlds

identity-sequence-return :
  ∀ {W head n U V} →
  TerminalStable head →
  head n ≡ returned U V →
  sequence W head immediateReturn
    (suc (suc n)) ≡ returned U V
identity-sequence-return
    {W} {head} {n} {U} {V}
    stable head-eq =
  sequence-after-return
    {W = W} {head = head}
    {continuation = immediateReturn}
    {n = suc n} {U = U} {V = V}
    (terminal-stable-at-right-sum
      {computation = head} {n = n}
      {o = returned U V}
      stable terminal-return head-eq (suc zero))

identity-sequence-return-invert :
  ∀ {W head n U V} →
  sequence W head immediateReturn
    n ≡ returned U V →
  Σ[ m ∈ StepIndex ]
    head m ≡ returned U V
identity-sequence-return-invert {n = zero} ()
identity-sequence-return-invert
    {head = head} {n = suc n}
    result-eq
    with head n in head-eq
identity-sequence-return-invert result-eq
    | timed Z =
  ⊥-elim (timed≢returned result-eq)
identity-sequence-return-invert result-eq
    | blamed Z =
  ⊥-elim (blamed≢returned result-eq)
identity-sequence-return-invert result-eq
    | failed Z e =
  ⊥-elim (failed≢returned result-eq)
identity-sequence-return-invert
    {n = suc zero} result-eq
    | returned Z Q =
  ⊥-elim (timed≢returned result-eq)
identity-sequence-return-invert
    {n = suc (suc n)} refl
    | returned Z Q =
  suc n , head-eq

immediate-return-error-impossible :
  ∀ W V {n U e} →
  immediateReturn W V n ≡ failed U e →
  ⊥
immediate-return-error-impossible W V {n = zero} ()
immediate-return-error-impossible W V {n = suc n} ()

right-identity-undelay :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R left
    (sequence W′ right immediateReturn) →
  TerminalStable right →
  TerminalSimulation value-result R left right
right-identity-undelay
    {W′ = W′} {value-result = value-result} {R = R}
    {left = left} {right = right}
    simulation right-stable′ =
  record
    { left-stable = left-stable simulation
    ; right-stable = right-stable′
    ; forward-return =
        λ { {n} {U} {V} eq →
          forward-return′ eq
        }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          backward-return simulation
            (identity-sequence-return
              {W = W′} {head = right}
              {n = n} {U = U′} {V = V′}
              right-stable′ eq)
        }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          target-blame-reflects simulation
            (sequence-head-blame
              {W = W′} {head = right}
              {continuation = immediateReturn}
              eq)
        }
    ; left-error-impossible = left-error-impossible simulation
    ; right-error-impossible =
        λ { {n} {U′} {e} eq →
          right-error-impossible simulation
            (sequence-head-error
              {W = W′} {head = right}
              {continuation = immediateReturn}
              eq)
        }
    }
  where
  forward-return′ :
    ∀ {n U V} →
    left n ≡ returned U V →
    Σ[ m ∈ StepIndex ]
    Σ[ U′ ∈ World ]
    Σ[ V′ ∈ Value ]
    Σ[ S ∈ WorldRelation U U′ ]
      WorldExtension R S ×
      right m ≡ returned U′ V′ ×
      value-result S V V′
  forward-return′ eq
      with forward-return simulation eq
  forward-return′ eq
      | m , U′ , V′ , S , R≤S , delayed-eq , V~V′
      with identity-sequence-return-invert
        {W = W′} {head = right}
        {n = m} {U = U′} {V = V′}
        delayed-eq
  forward-return′ eq
      | m , U′ , V′ , S , R≤S , delayed-eq , V~V′
      | q , right-eq =
    q , U′ , V′ , S , R≤S , right-eq , V~V′

left-sequence-simulation :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {left-continuation : World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (immediateReturn U′ V′)) →
  (∀ U V → TerminalStable (left-continuation U V)) →
  TerminalSimulation continuation-result R
    (sequence W left-head left-continuation)
    right-head
left-sequence-simulation
    {W} {W′}
    {head-result = head-result}
    {continuation-result = continuation-result}
    {R = R}
    {left-head} {right-head} {left-continuation}
    head-simulation continuation-simulation
    left-continuation-stable =
  right-identity-undelay
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = left-head} {right-head = right-head}
      {left-continuation = left-continuation}
      {right-continuation = immediateReturn}
      head-simulation continuation-simulation
      left-continuation-stable
      immediate-return-terminal-stable
      (λ { {n} {Z′} {e} eq →
        sequence-right-error-impossible
          {W = W} {W′ = W′}
          {head-result = head-result}
          {continuation-result = continuation-result}
          {R = R}
          {left-head = left-head} {right-head = right-head}
          {left-continuation = left-continuation}
          {right-continuation = immediateReturn}
          head-simulation
          immediate-return-error-impossible
          {n = n} {Z′ = Z′} {e = e} eq
        }))
    (right-stable head-simulation)

identity-sequence-blame-invert :
  ∀ {W head n U} →
  sequence W head immediateReturn n ≡ blamed U →
  Σ[ m ∈ StepIndex ]
    head m ≡ blamed U
identity-sequence-blame-invert {n = zero} ()
identity-sequence-blame-invert
    {head = head} {n = suc n}
    result-eq
    with head n in head-eq
identity-sequence-blame-invert result-eq
    | timed Z =
  ⊥-elim (timed≢blamed result-eq)
identity-sequence-blame-invert refl
    | blamed Z =
  _ , head-eq
identity-sequence-blame-invert result-eq
    | failed Z e =
  ⊥-elim (blamed≢failed (sym result-eq))
identity-sequence-blame-invert
    {n = suc zero} result-eq
    | returned Z Q =
  ⊥-elim (timed≢blamed result-eq)
identity-sequence-blame-invert
    {n = suc (suc n)} result-eq
    | returned Z Q =
  ⊥-elim (blamed≢returned (sym result-eq))

left-identity-undelay :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left right : Computation} →
  TerminalSimulation value-result R
    (sequence W left immediateReturn) right →
  TerminalStable left →
  TerminalSimulation value-result R left right
left-identity-undelay
    {W = W} {value-result = value-result} {R = R}
    {left = left} {right = right}
    simulation left-stable′ =
  record
    { left-stable = left-stable′
    ; right-stable = right-stable simulation
    ; forward-return =
        λ { {n} {U} {V} eq →
          forward-return simulation
            (identity-sequence-return
              {W = W} {head = left}
              {n = n} {U = U} {V = V}
              left-stable′ eq)
        }
    ; backward-return =
        λ { {n} {U′} {V′} eq →
          backward-return′ eq
        }
    ; target-blame-reflects =
        λ { {n} {U′} eq →
          target-blame-reflects′ eq
        }
    ; left-error-impossible =
        λ { {n} {U} {e} eq →
          left-error-impossible simulation
            (sequence-head-error
              {W = W} {head = left}
              {continuation = immediateReturn}
              eq)
        }
    ; right-error-impossible = right-error-impossible simulation
    }
  where
  backward-return′ :
    ∀ {n U′ V′} →
    right n ≡ returned U′ V′ →
    (Σ[ m ∈ StepIndex ]
     Σ[ U ∈ World ]
     Σ[ V ∈ Value ]
     Σ[ S ∈ WorldRelation U U′ ]
       WorldExtension R S ×
       left m ≡ returned U V ×
       value-result S V V′)
    ⊎
    (Σ[ m ∈ StepIndex ]
     Σ[ U ∈ World ]
       left m ≡ blamed U)
  backward-return′ eq
      with backward-return simulation eq
  backward-return′ eq
      | inj₁
          (m , U , V , S , R≤S , delayed-eq , V~V′)
      with identity-sequence-return-invert
        {W = W} {head = left}
        {n = m} {U = U} {V = V}
        delayed-eq
  backward-return′ eq
      | inj₁
          (m , U , V , S , R≤S , delayed-eq , V~V′)
      | q , left-eq =
    inj₁ (q , U , V , S , R≤S , left-eq , V~V′)
  backward-return′ eq
      | inj₂ (m , U , delayed-eq)
      with identity-sequence-blame-invert
        {W = W} {head = left}
        {n = m} {U = U}
        delayed-eq
  backward-return′ eq
      | inj₂ (m , U , delayed-eq)
      | q , left-eq =
    inj₂ (q , U , left-eq)

  target-blame-reflects′ :
    ∀ {n U′} →
    right n ≡ blamed U′ →
    Σ[ m ∈ StepIndex ]
    Σ[ U ∈ World ]
      left m ≡ blamed U
  target-blame-reflects′ eq
      with target-blame-reflects simulation eq
  target-blame-reflects′ eq
      | m , U , delayed-eq
      with identity-sequence-blame-invert
        {W = W} {head = left}
        {n = m} {U = U}
        delayed-eq
  target-blame-reflects′ eq
      | m , U , delayed-eq
      | q , left-eq =
    q , U , left-eq

right-sequence-simulation :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head : Computation}
    {right-continuation : World → Value → Computation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (immediateReturn U V)
      (right-continuation U′ V′)) →
  (∀ U′ V′ → TerminalStable (right-continuation U′ V′)) →
  (∀ {n Z′ e} →
    sequence W′ right-head right-continuation n ≡ failed Z′ e →
    ⊥) →
  TerminalSimulation continuation-result R
    left-head
    (sequence W′ right-head right-continuation)
right-sequence-simulation
    {W} {W′}
    {head-result = head-result}
    {continuation-result = continuation-result}
    {R = R}
    {left-head} {right-head} {right-continuation}
    head-simulation continuation-simulation
    right-continuation-stable right-sequence-error-free =
  left-identity-undelay
    (sequence-simulation
      {W = W} {W′ = W′} {R = R}
      {left-head = left-head} {right-head = right-head}
      {left-continuation = immediateReturn}
      {right-continuation = right-continuation}
      head-simulation continuation-simulation
      immediate-return-terminal-stable
      right-continuation-stable
      (λ { {n} {Z′} {e} eq →
        right-sequence-error-free
          {n = n} {Z′ = Z′} {e = e} eq
        }))
    (left-stable head-simulation)
