module proof.InterpreterFunctionProxyTail where

-- File Charter:
--   * Defines the two-phase computation after a proxy domain cast returns.
--   * Proves the direct proxy-application equation and terminal stability.
--   * Contains no narrowing, typing, or reduction argument.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (trans)

import Coercions
open import Interpreter
open import Core.InterpreterFuel using
  (applyValue-terminal-stable; coerceValue-terminal-stable)
open import Core.InterpreterOutcome
open import Simulation.Core.InterpreterSimulationResult

function-proxy-continuation :
  TypeEnvironment →
  Coercions.Coercion →
  World →
  Value →
  Computation
function-proxy-continuation θ q W V =
  coerceValue W θ q V

function-proxy-tail :
  TypeEnvironment →
  Coercions.Coercion →
  Value →
  World →
  Value →
  Computation
function-proxy-tail θ q V W U =
  chain
    (applyValue W V U)
    (function-proxy-continuation θ q)

function-proxy-tail-after-blame :
  ∀ {W θ q V U n Z} →
  applyValue W V U n ≡ blamed Z →
  function-proxy-tail θ q V W U n ≡ blamed Z
function-proxy-tail-after-blame
    {W} {θ} {q} {V} {U} {n} apply-eq
    with applyValue W V U n
function-proxy-tail-after-blame refl | blamed Z =
  refl

function-proxy-tail-after-error :
  ∀ {W θ q V U n Z e} →
  applyValue W V U n ≡ failed Z e →
  function-proxy-tail θ q V W U n ≡ failed Z e
function-proxy-tail-after-error
    {W} {θ} {q} {V} {U} {n} apply-eq
    with applyValue W V U n
function-proxy-tail-after-error refl | failed Z e =
  refl

function-proxy-tail-after-return :
  ∀ {W θ q V U n Z Q} →
  applyValue W V U n ≡ returned Z Q →
  function-proxy-tail θ q V W U n ≡
    coerceValue Z θ q Q n
function-proxy-tail-after-return
    {W} {θ} {q} {V} {U} {n} apply-eq
    with applyValue W V U n
function-proxy-tail-after-return refl | returned Z Q =
  refl

function-proxy-tail-stable :
  ∀ {W θ q V U} →
  TerminalStable (function-proxy-tail θ q V W U)
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    with applyValue W V U n in apply-eq
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | timed Z =
  ⊥-elim (timed-terminal-absurd eq terminal)
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | blamed Z
    =
  trans
    (function-proxy-tail-after-blame
      {W = W} {θ = θ} {q = q} {V = V} {U = U}
      {n = n Data.Nat.+ k} {Z = Z}
      (applyValue-terminal-stable
        {W = W} {V = V} {U = U}
        {n = n} {o = blamed Z}
        terminal-blame apply-eq k))
    eq
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | failed Z e
    =
  trans
    (function-proxy-tail-after-error
      {W = W} {θ = θ} {q = q} {V = V} {U = U}
      {n = n Data.Nat.+ k} {Z = Z} {e = e}
      (applyValue-terminal-stable
        {W = W} {V = V} {U = U}
        {n = n} {o = failed Z e}
        terminal-error apply-eq k))
    eq
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | returned Z Q
    with coerceValue Z θ q Q n in coerce-eq
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | returned Z Q | timed T =
  ⊥-elim (timed-terminal-absurd eq terminal)
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | returned Z Q | blamed T
    =
  trans
    (function-proxy-tail-after-return
      {W = W} {θ = θ} {q = q} {V = V} {U = U}
      {n = n Data.Nat.+ k} {Z = Z} {Q = Q}
      (applyValue-terminal-stable
        {W = W} {V = V} {U = U}
        {n = n} {o = returned Z Q}
        terminal-return apply-eq k))
    (trans
      (coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = Q}
        {n = n} {o = blamed T}
        terminal-blame coerce-eq k)
      eq)
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | returned Z Q | failed T e
    =
  trans
    (function-proxy-tail-after-return
      {W = W} {θ = θ} {q = q} {V = V} {U = U}
      {n = n Data.Nat.+ k} {Z = Z} {Q = Q}
      (applyValue-terminal-stable
        {W = W} {V = V} {U = U}
        {n = n} {o = returned Z Q}
        terminal-return apply-eq k))
    (trans
      (coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = Q}
        {n = n} {o = failed T e}
        terminal-error coerce-eq k)
      eq)
function-proxy-tail-stable
    {W} {θ} {q} {V} {U} {n} {o} terminal eq k
    | returned Z Q | returned T P
    =
  trans
    (function-proxy-tail-after-return
      {W = W} {θ = θ} {q = q} {V = V} {U = U}
      {n = n Data.Nat.+ k} {Z = Z} {Q = Q}
      (applyValue-terminal-stable
        {W = W} {V = V} {U = U}
        {n = n} {o = returned Z Q}
        terminal-return apply-eq k))
    (trans
      (coerceValue-terminal-stable
        {W = Z} {θ = θ} {c = q} {V = Q}
        {n = n} {o = returned T P}
        terminal-return coerce-eq k)
      eq)

function-proxy-computation-eq :
  ∀ {W θ p q V U} n →
  applyValue W (function-proxy p q θ V) U n ≡
  sequence W
    (coerceValue W θ p U)
    (λ Z Q → function-proxy-tail θ q V Z Q)
    n
function-proxy-computation-eq zero =
  refl
function-proxy-computation-eq
    {W} {θ} {p} {q} {V} {U} (suc n)
    with coerceValue W θ p U n
function-proxy-computation-eq (suc n) | timed Z =
  refl
function-proxy-computation-eq (suc n) | blamed Z =
  refl
function-proxy-computation-eq (suc n) | failed Z e =
  refl
function-proxy-computation-eq
    {W} {θ} {p} {q} {V} {U} (suc n)
    | returned Z Q
    with applyValue Z V Q n
function-proxy-computation-eq
    (suc n) | returned Z Q | timed T =
  refl
function-proxy-computation-eq
    (suc n) | returned Z Q | blamed T =
  refl
function-proxy-computation-eq
    (suc n) | returned Z Q | failed T e =
  refl
function-proxy-computation-eq
    (suc n) | returned Z Q | returned T P =
  refl
