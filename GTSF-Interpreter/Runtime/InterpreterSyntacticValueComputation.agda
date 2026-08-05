module Runtime.InterpreterSyntacticValueComputation where

-- File Charter:
--   * Characterizes direct interpretation of official syntactic values.
--   * Proves that a returned result is the value produced by `closeValue`.
--   * Proves that interpreting a syntactic value can never blame.
--   * Delegates the structural proof to a reduction-free private module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Maybe using (just)
open import Data.Product using (_×_)

open import Interpreter
import NuTerms as N
import proof.InterpreterSyntacticValueComputationProof as Proof


syntactic-value-return-unique :
  ∀ {W U γ θ M V V′ n}
    (vM : N.Value M) →
  closeValue vM γ θ ≡ just V →
  interpret W γ θ M n ≡ returned U V′ →
  (U ≡ W) × (V′ ≡ V)
syntactic-value-return-unique
    {W} {U} {γ} {θ} {M} {V} {V′} {n}
    vM close-eq result-eq =
  Proof.syntactic-value-return-unique
    {W = W} {U = U} {γ = γ} {θ = θ}
    {M = M} {V = V} {V′ = V′} {n = n}
    vM close-eq result-eq


syntactic-value-never-blames :
  ∀ {W U γ θ M n} →
  N.Value M →
  interpret W γ θ M n ≡ blamed U →
  ⊥
syntactic-value-never-blames
    {W} {U} {γ} {θ} {M} {n} vM blame-eq =
  Proof.syntactic-value-never-blames
    {W = W} {U = U} {γ = γ} {θ = θ} {M = M} {n = n}
    vM blame-eq
