module InterpreterAdequacy.proof.EventualReturnProblem where

-- File Charter:
--   * Packages the four mutually recursive completeness obligations at one
--     explicit small-step trace length.
--   * Keeps typing and trace-agreement evidence with each interpreter entry
--     point, while `Successful` records only the finite returned run.
--   * Supplies the constructor-form index used by the well-founded driver.

open import Agda.Builtin.Equality using (_≡_)
open import Data.List using (List; []; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _<_; zero)
open import Data.Product using (Σ-syntax)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import Typing.InterpreterSemanticTypingCore
open import SmallStepInterface.InterpreterTermShape using (InterpreterTerm)
open import Narrowing.InterpreterWorldNarrowing using (Allocated)
open import NuReduction using (StoreChanges; _—↠[_]_)
import NuTerms as N
open import Types using (TyCtx)

data ReturnProblem : ℕ → Set₂ where
  interpret-problem :
    ∀ {measure W prefix Δ Σ Γ γ θ M P A changes v} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    EnvironmentTyping W θ γ Γ →
    InterpreterTerm M →
    N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
    TermTraceAgreement world-agreement [] γ θ M P →
    P —↠[ changes ] v →
    N.Value v →
    ReturnProblem measure

  apply-problem :
    ∀ {measure W prefix F f U u A B changes v} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    ValueTyping W F (A ⇒ᵛ B) →
    ValueTyping W U A →
    ValueTraceAgreement world-agreement [] F f →
    ValueTraceAgreement world-agreement [] U u →
    (f N.· u) —↠[ changes ] v →
    N.Value v →
    ReturnProblem measure

  instantiate-problem :
    ∀ {measure W prefix α F f A changes v} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    Allocated W α →
    ValueTyping W F (polymorphic-type A) →
    lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
    ValueTraceAgreement world-agreement [] F f →
    (f N.•) —↠[ changes ] v →
    N.Value v →
    ReturnProblem measure

  coerce-problem :
    ∀ {measure W prefix Δ Σ θ τ c V u A B μ changes v} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B →
    ValueTyping W V ⟦ A ⟧[ θ ] →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    ValueTraceAgreement world-agreement [] V u →
    (u N.⟨ C.renameᶜ τ c ⟩) —↠[ changes ] v →
    N.Value v →
    ReturnProblem measure

Successful : ∀ {measure} → ReturnProblem measure → Set
Successful (interpret-problem {W = W} {γ = γ} {θ = θ} {M = M}
    measure-eq world-agreement W⊢ runtime runtime-env γ⊢
    image M⊢ M-agrees trace vV) =
  Σ[ n ∈ StepIndex ]
  Σ[ U ∈ World ]
  Σ[ V ∈ Value ] interpret W γ θ M n ≡ returned U V
Successful (apply-problem {W = W} {F = F} {U = U}
    measure-eq world-agreement W⊢ F⊢ U⊢ F-agrees U-agrees trace vV) =
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ V ∈ Value ] applyValue W F U n ≡ returned Z V
Successful (instantiate-problem {W = W} {α = α} {F = F}
    measure-eq world-agreement W⊢ allocation-ok F⊢ newest F-agrees
    trace vV) =
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ V ∈ Value ] instantiateValue W α F n ≡ returned Z V
Successful (coerce-problem {W = W} {θ = θ} {c = c} {V = V}
    measure-eq world-agreement W⊢ runtime runtime-env c⊢ V⊢
    θ-agrees V-agrees trace vV) =
  Σ[ n ∈ StepIndex ]
  Σ[ Z ∈ World ]
  Σ[ U ∈ Value ] coerceValue W θ c V n ≡ returned Z U

StrictlySmallerSolver : ℕ → Set₂
StrictlySmallerSolver measure =
  ∀ {smaller} →
  smaller < measure →
  (problem : ReturnProblem smaller) →
  Successful problem
