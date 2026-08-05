module InterpreterAdequacy.proof.EventualBlameDriver where

-- File Charter:
--   * Solves every packaged blame-completeness problem by well-founded
--     induction on the supplied finite trace length.
--   * Dispatches interpreter, application, instantiation, and coercion roots
--     to their constructive blame-completeness layers.
--   * Exports the total `eventual-blame` solver and assumes no normalization.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_; length)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (subst)

open import InterpreterAdequacy.proof.EventualApplyBlameLayer using
  (complete-apply-blame-after-root)
open import InterpreterAdequacy.proof.EventualBlameProblem
open import InterpreterAdequacy.proof.EventualCoerceBlameLayer using
  (complete-coerce-blame-after-root)
open import InterpreterAdequacy.proof.EventualInstantiateBlameLayer using
  (complete-instantiate-blame-after-root)
open import InterpreterAdequacy.proof.EventualInterpretBlameLayer using
  (complete-interpret-blame)
open import InterpreterAdequacy.proof.EventualReturnDriver using
  (bullet-value-step-is-keep)
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction

solve-blame-problem :
  ∀ {measure} →
  StrictlySmallerBlameSolver measure →
  (problem : BlameProblem measure) →
  Blames problem
solve-blame-problem solver
    (interpret-problem measure-eq world-agreement W⊢ runtime
      runtime-env environment image M⊢ M-agrees trace) =
  complete-interpret-blame solver measure-eq world-agreement W⊢ runtime
    runtime-env environment image M⊢ M-agrees trace
solve-blame-problem {measure = measure} solver
    (apply-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ F⊢ U⊢ F-agrees U-agrees
      (↠-step root tail)) =
  complete-apply-blame-after-root {measure = measure}
    solver world-agreement W⊢ F⊢ U⊢ F-agrees U-agrees root tail
    tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))
solve-blame-problem solver
    (instantiate-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ allocated-ok F⊢ newest F-agrees
      (↠-step root tail))
    with bullet-value-step-is-keep (value-trace-value F-agrees) root
solve-blame-problem solver
    (instantiate-problem {changes = .keep ∷ changes}
      measure-eq world-agreement W⊢ allocated-ok F⊢ newest F-agrees
      (↠-step root tail))
    | refl =
  complete-instantiate-blame-after-root solver world-agreement W⊢
    allocated-ok F⊢ newest F-agrees root tail tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))
solve-blame-problem {measure = measure} solver
    (coerce-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ runtime runtime-env c⊢ V⊢
      θ-agrees V-agrees (↠-step root tail)) =
  complete-coerce-blame-after-root solver world-agreement W⊢ runtime
    runtime-env c⊢ V⊢ θ-agrees V-agrees root tail tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))

solve-blame-problem-acc :
  ∀ {measure} →
  Acc _<_ measure →
  (problem : BlameProblem measure) →
  Blames problem
solve-blame-problem-acc (acc descend) problem =
  solve-blame-problem
    (λ smaller smaller-problem →
      solve-blame-problem-acc (descend smaller) smaller-problem)
    problem

eventual-blame :
  ∀ {measure} →
  (problem : BlameProblem measure) →
  Blames problem
eventual-blame {measure} problem =
  solve-blame-problem-acc (<-wellFounded measure) problem
