module InterpreterFuel where

-- File Charter:
--   * Exposes terminal fuel stabilization for every direct-interpreter entry.
--   * Shows that a terminal observation at a smaller index is incompatible
--     with timeout at a larger index.
--   * Delegates the mutual recursion to `proof.InterpreterFuelCore`.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Nat using (_≤_; _+_)
open import Data.Nat.Properties using
  (+-comm; +-suc; m≤n⇒∃[o]m+o≡n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Interpreter
open import InterpreterOutcome
import proof.InterpreterFuelCore as Proof

interpret-terminal-stable :
  ∀ {W γ θ M n o} →
  Terminal o →
  interpret W γ θ M n ≡ o →
  (k : StepIndex) →
  interpret W γ θ M (n + k) ≡ o
interpret-terminal-stable {n = n} =
  Proof.interpret-terminal-stableᵖ n

applyValue-terminal-stable :
  ∀ {W V U n o} →
  Terminal o →
  applyValue W V U n ≡ o →
  (k : StepIndex) →
  applyValue W V U (n + k) ≡ o
applyValue-terminal-stable {n = n} =
  Proof.applyValue-terminal-stableᵖ n

instantiateValue-terminal-stable :
  ∀ {W α V n o} →
  Terminal o →
  instantiateValue W α V n ≡ o →
  (k : StepIndex) →
  instantiateValue W α V (n + k) ≡ o
instantiateValue-terminal-stable {n = n} =
  Proof.instantiateValue-terminal-stableᵖ n

coerceValue-terminal-stable :
  ∀ {W θ c V n o} →
  Terminal o →
  coerceValue W θ c V n ≡ o →
  (k : StepIndex) →
  coerceValue W θ c V (n + k) ≡ o
coerceValue-terminal-stable {n = n} =
  Proof.coerceValue-terminal-stableᵖ n

run-terminal-stable :
  ∀ {N n o} →
  Terminal o →
  run N n ≡ o →
  (k : StepIndex) →
  run N (n + k) ≡ o
run-terminal-stable {N = N} {n = n} =
  Proof.interpret-terminal-stableᵖ n

future-index-swap :
  ∀ m n →
  m + (Data.Nat.suc n) ≡ n + (Data.Nat.suc m)
future-index-swap m n =
  trans (+-suc m n)
    (trans (cong Data.Nat.suc (+-comm m n))
      (sym (+-suc n m)))

run-terminal-after :
  ∀ {N m o} →
  Terminal o →
  run N m ≡ o →
  (n : StepIndex) →
  run N (n + (Data.Nat.suc m)) ≡ o
run-terminal-after {N = N} {m = m} {o = o}
    terminal terminal-eq n =
  subst (λ index → run N index ≡ o)
    (future-index-swap m n)
    (run-terminal-stable
      {N = N} {n = m} {o = o}
      terminal terminal-eq (Data.Nat.suc n))

terminal-before-timeout-impossible :
  ∀ {N m n o W} →
  m ≤ n →
  Terminal o →
  run N m ≡ o →
  run N n ≡ timed W →
  ⊥
terminal-before-timeout-impossible {N} {m} {n} {o} {W}
    m≤n terminal terminal-eq timeout-eq
    with m≤n⇒∃[o]m+o≡n m≤n
terminal-before-timeout-impossible {N} {m} {n} {o} {W}
    m≤n terminal terminal-eq timeout-eq
    | k , m+k≡n =
  terminal-not-timed terminal
    (trans
      (sym
        (subst
          (λ index → run N index ≡ o)
          m+k≡n
          (run-terminal-stable
            {N = N} {n = m} {o = o}
            terminal terminal-eq k)))
      timeout-eq)
