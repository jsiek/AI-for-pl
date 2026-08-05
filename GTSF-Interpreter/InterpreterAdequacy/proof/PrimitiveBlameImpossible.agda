module InterpreterAdequacy.proof.PrimitiveBlameImpossible where

-- File Charter:
--   * Proves that primitive interpretation never produces blame.
--   * Exhausts the interpreter's runtime value grammar directly.
--   * Contains no trace, reduction, or recursive interpreter reasoning.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

open import Interpreter using
  ( Value
  ; applyPrimitive
  ; blamed
  ; closure
  ; constant
  ; forall-proxy
  ; function-proxy
  ; generalized
  ; sealed
  ; tagged
  ; type-abstraction
  )
open import Primitives using (addℕ; κℕ)

apply-primitive-not-blamed :
  ∀ {W op F U Z} →
  applyPrimitive W op F U ≡ blamed Z →
  ⊥
apply-primitive-not-blamed {op = addℕ} {F = closure M γ θ} ()
apply-primitive-not-blamed {op = addℕ} {F = tagged gG θ F} ()
apply-primitive-not-blamed {op = addℕ} {F = sealed α F} ()
apply-primitive-not-blamed {op = addℕ} {F = function-proxy p q θ F} ()
apply-primitive-not-blamed {op = addℕ} {F = type-abstraction X F} ()
apply-primitive-not-blamed {op = addℕ} {F = forall-proxy c θ F} ()
apply-primitive-not-blamed {op = addℕ} {F = generalized A c θ F} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = closure M γ θ} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = constant (κℕ k)} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = tagged gG θ U} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = sealed α U} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = function-proxy p q θ U} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = type-abstraction X U} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = forall-proxy c θ U} ()
apply-primitive-not-blamed {op = addℕ} {F = constant (κℕ m)}
    {U = generalized A c θ U} ()
