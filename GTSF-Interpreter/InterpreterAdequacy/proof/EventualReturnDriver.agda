module InterpreterAdequacy.proof.EventualReturnDriver where

-- File Charter:
--   * Solves every packaged return-completeness problem by well-founded
--     induction on the supplied finite trace length.
--   * Dispatches interpreter, application, instantiation, and coercion roots
--     to their constructive completeness layers.
--   * Exports the total `eventual-return` solver and assumes no normalization.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_; length)
open import Data.Nat using (_<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (n<1+n)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (subst)

open import InterpreterAdequacy.proof.EventualApplyLayer using
  (complete-apply-after-root)
open import InterpreterAdequacy.proof.EventualCoerceLayer using
  (complete-coerce-after-root; complete-coerce-refl)
open import InterpreterAdequacy.proof.EventualInstantiateLayer using
  (complete-instantiate-after-root)
open import InterpreterAdequacy.proof.EventualInterpretLayer using
  (complete-interpret)
open import InterpreterAdequacy.proof.EventualReturnProblem
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-value)
open import NuReduction
import NuTerms as N

bullet-value-step-is-keep :
  ∀ {f change next} →
  N.Value f →
  (f N.•) —→[ change ] next →
  change ≡ keep
bullet-value-step-is-keep vf (pure-step (β-Λ• vF)) = refl
bullet-value-step-is-keep vf (pure-step (β-∀• vF)) = refl
bullet-value-step-is-keep vf (pure-step (β-gen• vF)) = refl
bullet-value-step-is-keep () (pure-step blame-•)

solve-return-problem :
  ∀ {measure} →
  StrictlySmallerSolver measure →
  (problem : ReturnProblem measure) →
  Successful problem
solve-return-problem solver
    (interpret-problem measure-eq world-agreement W⊢ runtime
      runtime-env environment image M⊢ M-agrees trace vV) =
  complete-interpret solver measure-eq world-agreement W⊢ runtime
    runtime-env environment image M⊢ M-agrees trace vV
solve-return-problem solver
    (apply-problem measure-eq world-agreement W⊢ F⊢ U⊢
      F-agrees U-agrees ↠-refl ())
solve-return-problem {measure = measure} solver
    (apply-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ F⊢ U⊢ F-agrees U-agrees
      (↠-step root tail) vV) =
  complete-apply-after-root {measure = measure}
    {changes = change ∷ changes} solver world-agreement W⊢ F⊢ U⊢
    F-agrees U-agrees root tail vV tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))
solve-return-problem solver
    (instantiate-problem measure-eq world-agreement W⊢ allocated F⊢
      newest F-agrees ↠-refl ())
solve-return-problem solver
    (instantiate-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ allocated F⊢ newest F-agrees
      (↠-step root tail) vV)
    with bullet-value-step-is-keep (value-trace-value F-agrees) root
solve-return-problem solver
    (instantiate-problem {changes = .keep ∷ changes}
      measure-eq world-agreement W⊢ allocated F⊢ newest F-agrees
      (↠-step root tail) vV)
    | refl =
  complete-instantiate-after-root solver world-agreement W⊢ allocated
    F⊢ newest F-agrees root tail vV tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))
solve-return-problem solver
    (coerce-problem measure-eq world-agreement W⊢ runtime runtime-env
      c⊢ V⊢ θ-agrees V-agrees ↠-refl vV) =
  complete-coerce-refl world-agreement W⊢ runtime runtime-env c⊢ V⊢
    θ-agrees V-agrees vV
solve-return-problem solver
    (coerce-problem {changes = change ∷ changes}
      measure-eq world-agreement W⊢ runtime runtime-env c⊢ V⊢
      θ-agrees V-agrees (↠-step root tail) vV) =
  complete-coerce-after-root solver world-agreement W⊢ runtime
    runtime-env c⊢ V⊢ θ-agrees V-agrees root tail vV tail-smaller
  where
  tail-smaller : length changes < _
  tail-smaller = subst (length changes <_) measure-eq
    (n<1+n (length changes))

solve-return-problem-acc :
  ∀ {measure} →
  Acc _<_ measure →
  (problem : ReturnProblem measure) →
  Successful problem
solve-return-problem-acc (acc descend) problem =
  solve-return-problem
    (λ smaller smaller-problem →
      solve-return-problem-acc (descend smaller) smaller-problem)
    problem

eventual-return :
  ∀ {measure} →
  (problem : ReturnProblem measure) →
  Successful problem
eventual-return {measure} problem =
  solve-return-problem-acc (<-wellFounded measure) problem
