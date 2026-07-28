module InterpreterObservations where

-- File Charter:
--   * Defines positive runtime observations for the fuel-indexed interpreter.
--   * Uses universal timeout evidence for divergence instead of negated
--     convergence.
--   * Exposes interpreter evaluation as an induced big-step relation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (∃-syntax)

open import Interpreter
open import NuTerms using (Term)

------------------------------------------------------------------------
-- Predicates on individual outcomes
------------------------------------------------------------------------

data IsTimeout : Outcome → Set where
  is-timeout :
    ∀ {W} →
    IsTimeout (timed W)

data IsBlame : Outcome → Set where
  is-blame :
    ∀ {W} →
    IsBlame (blamed W)

data IsError : Outcome → Set where
  is-error :
    ∀ {W e} →
    IsError (failed W e)

------------------------------------------------------------------------
-- Program observations
------------------------------------------------------------------------

infix 2 _⇓ᴵ[_]_

_⇓ᴵ[_]_ : Term → World → Value → Set
M ⇓ᴵ[ W ] V =
  ∃[ n ] (run M n ≡ returned W V)

Blamesᴵ : Term → Set
Blamesᴵ M =
  ∃[ n ] IsBlame (run M n)

Errorsᴵ : Term → Set
Errorsᴵ M =
  ∃[ n ] IsError (run M n)

-- This is positive evidence: every finite observation of the interpreter
-- reaches its timeout alternative. It is not `¬ Converges`.
Divergesᴵ : Term → Set
Divergesᴵ M =
  ∀ n →
  IsTimeout (run M n)
