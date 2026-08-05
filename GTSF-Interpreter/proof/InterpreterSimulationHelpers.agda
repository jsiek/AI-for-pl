module proof.InterpreterSimulationHelpers where

-- File Charter:
--   * Provides reduction-free algebra for constructive terminal simulation.
--   * Proves stability of the interpreter-shaped sequencing combinator and
--     combines independently delayed terminal observations at one fuel.
--   * Contains no syntax, coercion, or catch-up case analysis.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import Interpreter
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult
import Narrowing.InterpreterCoercionNarrowing as ICN
import Narrowing.InterpreterTermNarrowing as ITN
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties

open ITN.InterpreterValues
open ITN.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    ICN.InterpreterTypeNarrowing

terminal-stable-at-left-sum :
  ∀ {computation n o} →
  TerminalStable computation →
  Terminal o →
  computation n ≡ o →
  (k : StepIndex) →
  computation (n + k) ≡ o
terminal-stable-at-left-sum stable terminal eq k =
  stable terminal eq k

terminal-stable-at-right-sum :
  ∀ {computation n o} →
  TerminalStable computation →
  Terminal o →
  computation n ≡ o →
  (k : StepIndex) →
  computation (k + n) ≡ o
terminal-stable-at-right-sum
    {computation = computation} {n = n} {o = o}
    stable terminal eq k =
  subst
    (λ index → computation index ≡ o)
    (+-comm n k)
    (stable terminal eq k)

sequence-head-blame :
  ∀ {W head continuation m U} →
  head m ≡ blamed U →
  sequence W head continuation (suc m) ≡ blamed U
sequence-head-blame {head = head} {m = m}
    head-eq
    with head m in observed
sequence-head-blame refl
    | blamed U =
  refl

sequence-head-error :
  ∀ {W head continuation m U e} →
  head m ≡ failed U e →
  sequence W head continuation (suc m) ≡ failed U e
sequence-head-error {head = head} {m = m}
    head-eq
    with head m in observed
sequence-head-error refl
    | failed U e =
  refl

sequence-after-return :
  ∀ {W head continuation n U V} →
  head n ≡ returned U V →
  sequence W head continuation (suc n) ≡ continuation U V n
sequence-after-return {head = head} {n = n} head-eq
    with head n in observed
sequence-after-return refl | returned U V =
  refl

sequence-continuation-terminal :
  ∀ {W head continuation m q U V o} →
  TerminalStable head →
  TerminalStable (continuation U V) →
  head m ≡ returned U V →
  Terminal o →
  continuation U V q ≡ o →
  sequence W head continuation (suc (m + q)) ≡ o
sequence-continuation-terminal
    {W = W} {head = head} {continuation = continuation}
    {m = m} {q} {U} {V} {o}
    head-stable continuation-stable
    head-eq terminal continuation-eq =
  trans
    (sequence-after-return
      {W = W} {head = head} {continuation = continuation}
      {n = m + q} {U = U} {V = V}
      (head-stable terminal-return head-eq q))
    (terminal-stable-at-right-sum
      {computation = continuation U V}
      {n = q} {o = o}
      continuation-stable terminal continuation-eq m)

sequence-terminal-stable :
  ∀ {W head continuation} →
  TerminalStable head →
  (∀ U V → TerminalStable (continuation U V)) →
  TerminalStable (sequence W head continuation)
sequence-terminal-stable head-stable continuation-stable
    {n = zero} terminal eq k =
  ⊥-elim (timed-terminal-absurd eq terminal)
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    with head n in head-eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | timed U =
  ⊥-elim (timed-terminal-absurd eq terminal)
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | blamed U
    rewrite head-stable terminal-blame head-eq k =
  eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | failed U e
    rewrite head-stable terminal-error head-eq k =
  eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | returned U V
    with continuation U V n in continuation-eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | returned U V | timed Z =
  ⊥-elim (timed-terminal-absurd eq terminal)
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | returned U V | blamed Z
    rewrite head-stable terminal-return head-eq k
          | continuation-stable U V terminal-blame
              continuation-eq k =
  eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | returned U V | failed Z e
    rewrite head-stable terminal-return head-eq k
          | continuation-stable U V terminal-error
              continuation-eq k =
  eq
sequence-terminal-stable
    {W = W} {head} {continuation}
    head-stable continuation-stable
    {n = suc n} terminal eq k
    | returned U V | returned Z Q
    rewrite head-stable terminal-return head-eq k
          | continuation-stable U V terminal-return
              continuation-eq k =
  eq

chain-terminal-stable :
  ∀ {head continuation} →
  TerminalStable head →
  (∀ U V → TerminalStable (continuation U V)) →
  TerminalStable (chain head continuation)
chain-terminal-stable
    {head = head} {continuation = continuation}
    head-stable continuation-stable
    {n = n} {o = o} terminal eq k =
  sequence-terminal-stable
    {W = emptyWorld}
    {head = head}
    {continuation = continuation}
    head-stable continuation-stable
    {n = suc n} {o = o} terminal eq k

sequence-forward-return :
  ∀ {W W′}
    {head-result continuation-result : ValueResultRelation}
    {R : WorldRelation W W′}
    {left-head right-head}
    {left-continuation right-continuation} →
  (head-simulation :
    TerminalSimulation head-result R left-head right-head) →
  (∀ {U U′ V V′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    head-result S V V′ →
    TerminalSimulation continuation-result S
      (left-continuation U V)
      (right-continuation U′ V′)) →
  ∀ {n Z Q} →
  sequence W left-head left-continuation n ≡ returned Z Q →
  Data.Product.Σ StepIndex
    (λ m →
      Data.Product.Σ World
        (λ Z′ →
          Data.Product.Σ Value
            (λ Q′ →
              Data.Product.Σ (WorldRelation Z Z′)
                (λ T →
                  WorldExtension R T ×
                  sequence W′ right-head right-continuation m
                    ≡ returned Z′ Q′ ×
                  continuation-result T Q Q′))))
sequence-forward-return head-simulation continuation-simulation
    {n = zero} ()
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    with left-head n in head-eq
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | timed U =
  ⊥-elim (timed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | blamed U =
  ⊥-elim (blamed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | failed U e =
  ⊥-elim (failed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V
    with left-continuation U V n in continuation-eq
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | timed Z =
  ⊥-elim (timed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | blamed Z =
  ⊥-elim (blamed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | failed Z e =
  ⊥-elim (failed≢returned result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | returned Z Q
    with forward-return head-simulation head-eq
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    with forward-return
      (continuation-simulation R≤S V~V′)
      (trans continuation-eq result-eq)
sequence-forward-return
    {W = W} {W′} {head-result} {continuation-result}
    {R} {left-head} {right-head}
    {left-continuation} {right-continuation}
    head-simulation continuation-simulation
    {n = suc n} result-eq
    | returned U V | returned Z Q
    | m , U′ , V′ , S , R≤S , right-head-eq , V~V′
    | q , Z′ , Q′ , T , S≤T , right-continuation-eq , Q~Q′ =
  suc (m + q) , Z′ , Q′ , T ,
  WorldProof.world-extension-trans R≤S S≤T ,
  sequence-continuation-terminal
    {W = W′}
    {head = right-head}
    {continuation = right-continuation}
    {m = m} {q = q} {U = U′} {V = V′}
    {o = returned Z′ Q′}
    (right-stable head-simulation)
    (right-stable (continuation-simulation R≤S V~V′))
    right-head-eq terminal-return right-continuation-eq ,
  Q~Q′

immediate-return-terminal-stable :
  ∀ W V →
  TerminalStable (immediateReturn W V)
immediate-return-terminal-stable W V
    {n = zero} terminal eq k =
  ⊥-elim (timed-terminal-absurd eq terminal)
immediate-return-terminal-stable W V
    {n = suc n} terminal eq k =
  eq

immediate-return-simulation :
  ∀ {W W′ V V′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′} →
  value-result R V V′ →
  TerminalSimulation value-result R
    (immediateReturn W V)
    (immediateReturn W′ V′)
left-stable (immediate-return-simulation {W = W} {W′} V~V′) =
  immediate-return-terminal-stable W _
right-stable (immediate-return-simulation {W = W} {W′} V~V′) =
  immediate-return-terminal-stable W′ _
forward-return
    (immediate-return-simulation {W = W} {W′} V~V′)
    {n = zero} ()
forward-return
    (immediate-return-simulation {W = W} {W′} V~V′)
    {n = suc n} refl =
  suc zero , W′ , _ , _ ,
  extension-refl , refl , V~V′
backward-return
    (immediate-return-simulation {W = W} {W′} V~V′)
    {n = zero} ()
backward-return
    (immediate-return-simulation {W = W} {W′} V~V′)
    {n = suc n} refl =
  inj₁
    (suc zero , W , _ , _ ,
     extension-refl , refl , V~V′)
target-blame-reflects
    (immediate-return-simulation V~V′)
    {n = zero} ()
target-blame-reflects
    (immediate-return-simulation V~V′)
    {n = suc n} ()
left-error-impossible
    (immediate-return-simulation V~V′)
    {n = zero} ()
left-error-impossible
    (immediate-return-simulation V~V′)
    {n = suc n} ()
right-error-impossible
    (immediate-return-simulation V~V′)
    {n = zero} ()
right-error-impossible
    (immediate-return-simulation V~V′)
    {n = suc n} ()

immediate-blame-terminal-stable :
  ∀ W →
  TerminalStable (immediateBlame W)
immediate-blame-terminal-stable W
    {n = zero} terminal eq k =
  ⊥-elim (timed-terminal-absurd eq terminal)
immediate-blame-terminal-stable W
    {n = suc n} terminal eq k =
  eq

immediate-blame-simulation :
  ∀ {W W′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′} →
  TerminalSimulation value-result R
    (immediateBlame W)
    (immediateBlame W′)
left-stable (immediate-blame-simulation {W = W} {W′}) =
  immediate-blame-terminal-stable W
right-stable (immediate-blame-simulation {W = W} {W′}) =
  immediate-blame-terminal-stable W′
forward-return immediate-blame-simulation
    {n = zero} ()
forward-return immediate-blame-simulation
    {n = suc n} ()
backward-return immediate-blame-simulation
    {n = zero} ()
backward-return immediate-blame-simulation
    {n = suc n} ()
target-blame-reflects
    (immediate-blame-simulation {W = W} {W′})
    {n = zero} ()
target-blame-reflects
    (immediate-blame-simulation {W = W} {W′})
    {n = suc n} refl =
  suc zero , W , refl
left-error-impossible immediate-blame-simulation
    {n = zero} ()
left-error-impossible immediate-blame-simulation
    {n = suc n} ()
right-error-impossible immediate-blame-simulation
    {n = zero} ()
right-error-impossible immediate-blame-simulation
    {n = suc n} ()

fixed-outcome-stable :
  ∀ {o} →
  TerminalStable (fixedOutcome o)
fixed-outcome-stable terminal eq k =
  eq

fixed-terminal-stable :
  ∀ {o} →
  Terminal o →
  TerminalStable (fixedOutcome o)
fixed-terminal-stable fixed-terminal terminal eq k =
  eq

fixed-return-simulation :
  ∀ {W W′ V V′}
    {value-result : ValueResultRelation}
    {R : WorldRelation W W′} →
  value-result R V V′ →
  TerminalSimulation value-result R
    (fixedOutcome (returned W V))
    (fixedOutcome (returned W′ V′))
left-stable
    (fixed-return-simulation {W = W} {V = V} V~V′)
    terminal eq k =
  eq
right-stable
    (fixed-return-simulation {W′ = W′} {V′ = V′} V~V′)
    terminal eq k =
  eq
forward-return
    (fixed-return-simulation {W = W} {W′} V~V′)
    refl =
  zero , W′ , _ , _ ,
  extension-refl , refl , V~V′
backward-return
    (fixed-return-simulation {W = W} {W′} V~V′)
    refl =
  inj₁
    ( zero , W , _ , _ ,
      extension-refl , refl , V~V′
    )
target-blame-reflects
    (fixed-return-simulation V~V′) ()
left-error-impossible
    (fixed-return-simulation V~V′) ()
right-error-impossible
    (fixed-return-simulation V~V′) ()
