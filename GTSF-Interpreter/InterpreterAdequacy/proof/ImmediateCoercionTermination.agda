module InterpreterAdequacy.proof.ImmediateCoercionTermination where

-- File Charter:
--   * Proves that active untag and unseal coercions cannot time out at
--     positive fuel.
--   * Performs only the finite decision procedure built into `coerceValue`.
--   * Contains no reduction, trace, typing, or normalization dependency.

open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Empty
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc)
open import Relation.Nullary using (yes; no)

import Coercions as C
open import Interpreter

untag-positive-not-timed :
  ∀ {W θ G V n Z} →
  coerceValue W θ (G C.？) V (suc n) ≡ timed Z →
  Data.Empty.⊥
untag-positive-not-timed {W} {θ} {G} {V} {n}
    result-eq with ground? θ G
untag-positive-not-timed () | no not-ground
untag-positive-not-timed {W} {θ} {G} {V} {n}
    result-eq | yes runtime-ground
    with tagOf θ (runtime-ground-syntax runtime-ground)
untag-positive-not-timed () | yes runtime-ground | nothing
untag-positive-not-timed {V = closure N γ σ} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {V = type-abstraction X V} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {V = constant κ} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {W} {θ} {G}
    {V = tagged {G = H} gH σ V} {n}
    result-eq | yes runtime-ground | just expected
    with tagOf σ gH
untag-positive-not-timed ()
    | yes runtime-ground | just expected | nothing
untag-positive-not-timed result-eq
    | yes runtime-ground | just expected | just actual
    with expected ≟Tag actual
untag-positive-not-timed ()
    | yes runtime-ground | just expected | just .expected | yes refl
untag-positive-not-timed ()
    | yes runtime-ground | just expected | just actual | no tags-differ
untag-positive-not-timed {V = sealed α V} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {V = function-proxy p q σ V} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {V = forall-proxy c σ V} ()
    | yes runtime-ground | just expected
untag-positive-not-timed {V = generalized A c σ V} ()
    | yes runtime-ground | just expected

unseal-positive-not-timed :
  ∀ {W θ X A V n Z} →
  coerceValue W θ (C.unseal X A) V (suc n) ≡ timed Z →
  Data.Empty.⊥
unseal-positive-not-timed {W} {θ} {X} {A} {V} {n}
    result-eq with lookup θ X
unseal-positive-not-timed () | nothing
unseal-positive-not-timed () | just (abstract-name Y)
unseal-positive-not-timed {V = closure N γ σ} ()
    | just (seal-name α)
unseal-positive-not-timed {V = type-abstraction Y V} ()
    | just (seal-name α)
unseal-positive-not-timed {V = constant κ} ()
    | just (seal-name α)
unseal-positive-not-timed {V = tagged gG σ V} ()
    | just (seal-name α)
unseal-positive-not-timed {V = sealed β V} result-eq
    | just (seal-name α) with α ≟SealName β
unseal-positive-not-timed () | just (seal-name α) | yes refl
unseal-positive-not-timed () | just (seal-name α) | no names-differ
unseal-positive-not-timed {V = function-proxy p q σ V} ()
    | just (seal-name α)
unseal-positive-not-timed {V = forall-proxy c σ V} ()
    | just (seal-name α)
unseal-positive-not-timed {V = generalized B c σ V} ()
    | just (seal-name α)
