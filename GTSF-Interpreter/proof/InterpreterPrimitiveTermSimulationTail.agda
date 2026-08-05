module proof.InterpreterPrimitiveTermSimulationTail where

-- File Charter:
--   * Defines the interpreter computation following a returned left operand.
--   * Proves its direct equations, terminal stability, and typed error
--     exclusion.
--   * Contains no term-narrowing or reduction argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Interpreter
open import Typing.InterpreterErrorFreedom using
  (outcome-typing-excludes-error)
open import Core.InterpreterFuel using (interpret-terminal-stable)
open import Core.InterpreterOutcome
open import Typing.InterpreterSemanticTyping
open import Simulation.Core.InterpreterSimulationResult
import NuTerms as N
open import Primitives using (addℕ)
open import proof.InterpreterPrimitiveSimulationCases using
  (natural-value-canonical)
open import Types

primitive-continuation :
  Value →
  World →
  Value →
  Computation
primitive-continuation V W U =
  fixedOutcome (applyPrimitive W addℕ V U)

primitive-tail :
  World →
  Environment →
  TypeEnvironment →
  N.Term →
  Value →
  Computation
primitive-tail W γ θ M V =
  chain (interpret W γ θ M) (primitive-continuation V)

primitive-continuation-stable :
  ∀ V W U →
  TerminalStable (primitive-continuation V W U)
primitive-continuation-stable V W U terminal eq k =
  eq

primitive-tail-after-blame :
  ∀ {W γ θ M V n U} →
  interpret W γ θ M n ≡ blamed U →
  primitive-tail W γ θ M V n ≡ blamed U
primitive-tail-after-blame
    {W} {γ} {θ} {M} {V} {n} head-eq
    with interpret W γ θ M n
primitive-tail-after-blame refl | blamed U =
  refl

primitive-tail-after-error :
  ∀ {W γ θ M V n U e} →
  interpret W γ θ M n ≡ failed U e →
  primitive-tail W γ θ M V n ≡ failed U e
primitive-tail-after-error
    {W} {γ} {θ} {M} {V} {n} head-eq
    with interpret W γ θ M n
primitive-tail-after-error refl | failed U e =
  refl

primitive-tail-after-return :
  ∀ {W γ θ M V n U Q} →
  interpret W γ θ M n ≡ returned U Q →
  primitive-tail W γ θ M V n ≡ applyPrimitive U addℕ V Q
primitive-tail-after-return
    {W} {γ} {θ} {M} {V} {n} head-eq
    with interpret W γ θ M n
primitive-tail-after-return refl | returned U Q =
  refl

primitive-computation-eq :
  ∀ {W γ θ L M} n →
  interpret W γ θ (L N.⊕[ addℕ ] M) n ≡
  sequence W
    (interpret W γ θ L)
    (λ U V → primitive-tail U γ θ M V)
    n
primitive-computation-eq zero =
  refl
primitive-computation-eq {W} {γ} {θ} {L} {M} (suc n)
    with interpret W γ θ L n
primitive-computation-eq (suc n) | timed U =
  refl
primitive-computation-eq (suc n) | blamed U =
  refl
primitive-computation-eq (suc n) | failed U e =
  refl
primitive-computation-eq
    {W} {γ} {θ} {L} {M} (suc n) | returned u v
    with interpret u γ θ M n
primitive-computation-eq (suc n)
    | returned u v | timed z =
  refl
primitive-computation-eq (suc n)
    | returned u v | blamed z =
  refl
primitive-computation-eq (suc n)
    | returned u v | failed z e =
  refl
primitive-computation-eq (suc n)
    | returned u v | returned z q =
  refl

primitive-result-error-impossible :
  ∀ {W V U Z e} →
  ValueTyping W V (base-type `ℕ) →
  ValueTyping W U (base-type `ℕ) →
  applyPrimitive W addℕ V U ≡ failed Z e →
  ⊥
primitive-result-error-impossible V⊢ U⊢ result-eq
    with natural-value-canonical V⊢
       | natural-value-canonical U⊢
primitive-result-error-impossible V⊢ U⊢ result-eq
    | m , refl | n , refl =
  failed≢returned (sym result-eq)

primitive-tail-error-impossible :
  ∀ {W γ θ M V} →
  ValueTyping W V (base-type `ℕ) →
  (∀ n →
    OutcomeTyping W (base-type `ℕ)
      (interpret W γ θ M n)) →
  ∀ {n Z e} →
  primitive-tail W γ θ M V n ≡ failed Z e →
  ⊥
primitive-tail-error-impossible
    {W} {γ} {θ} {M} {V} V⊢ M-typing
    {n = n} result-eq
    with interpret W γ θ M n in head-eq
primitive-tail-error-impossible
    {W = W} {γ = γ} {θ = θ} {M = M}
    V⊢ M-typing {n = n} result-eq
    | timed U =
  timed≢failed result-eq
primitive-tail-error-impossible
    {W = W} {γ = γ} {θ = θ} {M = M}
    V⊢ M-typing {n = n} result-eq
    | blamed U =
  blamed≢failed result-eq
primitive-tail-error-impossible
    {W = W} {γ = γ} {θ = θ} {M = M}
    V⊢ M-typing {n = n} result-eq
    | failed U e =
  outcome-typing-excludes-error (M-typing n) head-eq
primitive-tail-error-impossible
    {W = W} {γ = γ} {θ = θ} {M = M}
    V⊢ M-typing {n = n} result-eq
    | returned u q
    with subst (OutcomeTyping W (base-type `ℕ))
      head-eq (M-typing n)
primitive-tail-error-impossible
    {W = W} {γ = γ} {θ = θ} {M = M}
    V⊢ M-typing {n = n} result-eq
    | returned u q | return-typed W≤U U⊢ Q⊢ =
  primitive-result-error-impossible
    (semantic-value-world-weaken W≤U U⊢ V⊢)
    Q⊢
    result-eq

primitive-tail-stable :
  ∀ {W γ θ M V} →
  TerminalStable
    (primitive-tail W γ θ M V)
primitive-tail-stable {W} {γ} {θ} {M} {V}
    {n} {o} terminal eq k
    with interpret W γ θ M n in head-eq
primitive-tail-stable
    {W} {γ} {θ} {M} {V} {n} {o} terminal eq k
    | timed U =
  ⊥-elim (timed-terminal-absurd eq terminal)
primitive-tail-stable
    {W} {γ} {θ} {M} {V} {n} {o} terminal eq k
    | blamed U
    =
  trans
    (primitive-tail-after-blame
      {W = W} {γ = γ} {θ = θ} {M = M} {V = V}
      {n = n Data.Nat.+ k} {U = U}
      (interpret-terminal-stable
        {W = W} {γ = γ} {θ = θ} {M = M}
        {n = n} {o = blamed U}
        terminal-blame head-eq k))
    eq
primitive-tail-stable
    {W} {γ} {θ} {M} {V} {n} {o} terminal eq k
    | failed U e
    =
  trans
    (primitive-tail-after-error
      {W = W} {γ = γ} {θ = θ} {M = M} {V = V}
      {n = n Data.Nat.+ k} {U = U} {e = e}
      (interpret-terminal-stable
        {W = W} {γ = γ} {θ = θ} {M = M}
        {n = n} {o = failed U e}
        terminal-error head-eq k))
    eq
primitive-tail-stable
    {W} {γ} {θ} {M} {V} {n} {o} terminal eq k
    | returned U Q
    =
  trans
    (primitive-tail-after-return
      {W = W} {γ = γ} {θ = θ} {M = M} {V = V}
      {n = n Data.Nat.+ k} {U = U} {Q = Q}
      (interpret-terminal-stable
        {W = W} {γ = γ} {θ = θ} {M = M}
        {n = n} {o = returned U Q}
        terminal-return head-eq k))
    eq
