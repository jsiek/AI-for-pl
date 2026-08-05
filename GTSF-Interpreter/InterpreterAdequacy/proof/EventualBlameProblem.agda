module InterpreterAdequacy.proof.EventualBlameProblem where

-- File Charter:
--   * Packages the four mutually recursive blame-completeness obligations at
--     one explicit small-step trace length.
--   * Carries typing and trace agreement for each interpreter entry point.
--   * Defines the constructor-form index used by the well-founded driver.

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

data BlameProblem : ℕ → Set₂ where
  interpret-problem :
    ∀ {measure W prefix Δ Σ Γ γ θ M P A changes} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    EnvironmentTyping W θ γ Γ →
    InterpreterTerm M →
    N._∣_∣_⊢_⦂_ Δ Σ Γ M A →
    TermTraceAgreement world-agreement [] γ θ M P →
    P —↠[ changes ] N.blame →
    BlameProblem measure

  apply-problem :
    ∀ {measure W prefix F f U u A B changes} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    ValueTyping W F (A ⇒ᵛ B) →
    ValueTyping W U A →
    ValueTraceAgreement world-agreement [] F f →
    ValueTraceAgreement world-agreement [] U u →
    (f N.· u) —↠[ changes ] N.blame →
    BlameProblem measure

  instantiate-problem :
    ∀ {measure W prefix α F f A changes} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    Allocated W α →
    ValueTyping W F (polymorphic-type A) →
    lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
    ValueTraceAgreement world-agreement [] F f →
    (f N.•) —↠[ changes ] N.blame →
    BlameProblem measure

  coerce-problem :
    ∀ {measure W prefix Δ Σ θ τ c V u A B μ changes} →
    length changes ≡ measure →
    (world-agreement : WorldTraceAgreement W prefix) →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeTypeEnvironment θ →
    C._∣_∣_⊢_∶_=⇒_ μ Δ Σ c A B →
    ValueTyping W V ⟦ A ⟧[ θ ] →
    TypeEnvironmentTraceAgreement world-agreement [] θ τ →
    ValueTraceAgreement world-agreement [] V u →
    (u N.⟨ C.renameᶜ τ c ⟩) —↠[ changes ] N.blame →
    BlameProblem measure

Blames : ∀ {measure} → BlameProblem measure → Set
Blames (interpret-problem {W = W} {γ = γ} {θ = θ} {M = M}
    measure-eq world-agreement W⊢ runtime runtime-env environment
    image M⊢ M-agrees trace) =
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ] interpret W γ θ M n ≡ blamed Z
Blames (apply-problem {W = W} {F = F} {U = U}
    measure-eq world-agreement W⊢ F⊢ U⊢ F-agrees U-agrees trace) =
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ] applyValue W F U n ≡ blamed Z
Blames (instantiate-problem {W = W} {α = α} {F = F}
    measure-eq world-agreement W⊢ allocated F⊢ newest F-agrees trace) =
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    instantiateValue W α F n ≡ blamed Z
Blames (coerce-problem {W = W} {θ = θ} {c = c} {V = V}
    measure-eq world-agreement W⊢ runtime runtime-env c⊢ V⊢
    θ-agrees V-agrees trace) =
  Σ[ n ∈ StepIndex ] Σ[ Z ∈ World ]
    coerceValue W θ c V n ≡ blamed Z

StrictlySmallerBlameSolver : ℕ → Set₂
StrictlySmallerBlameSolver measure =
  ∀ {smaller} →
  smaller < measure →
  (problem : BlameProblem smaller) →
  Blames problem
