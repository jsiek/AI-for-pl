module InterpreterAdequacy.proof.TraceAgreementAbstract where

-- File Charter:
--   * Inserts one abstract type name into a value trace context.
--   * Tracks the prefix of type abstractions owned by the value so nested
--     `Λ` values are renamed under their own binders correctly.
--   * Supplies the environment lifting used while closing a syntactic `Λ`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Coercions using (renameᶜ)
open import Interpreter using
  (Name; TypeEnvironment; Value; abstract-name; lookup)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementBind using
  ( insert-seal-renaming
  ; rename-environment
  ; environment-substitution-rename
  ; extended-environment-substitution-rename
  )
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-compose)
open import proof.Core.Properties.NuTermProperties using
  ( renameᵗᵐ-compose
  ; renameᵗᵐ-preserves-Value
  ; renameᵗᵐ-preserves-No•
  )
open import proof.Substitution.Term.TermSubstitutionSyntax using
  (substˣᵐ-renameᵗᵐ)
open import Types using (extᵗ)

lookup-after-abstract-insertion :
  ∀ Ω Ξ {W X i a} →
  lookup (visibleTypeNames (Ω ++ Ξ) W) i ≡ just a →
  lookup (visibleTypeNames (Ω ++ X ∷ Ξ) W)
    (insert-seal-renaming Ω i) ≡ just a
lookup-after-abstract-insertion [] Ξ old-lookup = old-lookup
lookup-after-abstract-insertion
    (Y ∷ Ω) Ξ {X = X} {i = zero} old-lookup =
  old-lookup
lookup-after-abstract-insertion
    (Y ∷ Ω) Ξ {W = W} {X = X} {i = suc i} {a = a} old-lookup =
  lookup-after-abstract-insertion
    Ω Ξ {W = W} {X = X} {i = i} {a = a} old-lookup

type-environment-trace-insert-abstract :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ω Ξ X θ τ} →
  TypeEnvironmentTraceAgreement world-agreement (Ω ++ Ξ) θ τ →
  TypeEnvironmentTraceAgreement world-agreement (Ω ++ X ∷ Ξ) θ
    (λ Y → insert-seal-renaming Ω (τ Y))
type-environment-trace-insert-abstract
    {W = W} {Ω = Ω} {Ξ = Ξ} {X = X} {τ = τ}
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement
    (λ {X = Y} {a = a} θ-lookup →
      lookup-after-abstract-insertion
        Ω Ξ {W = W} {X = X} {i = τ Y} {a = a}
        (lookup-agrees θ-lookup))

mutual
  value-trace-insert-abstract :
    ∀ {W χs}
      {world-agreement : WorldTraceAgreement W χs}
      {Ω Ξ X V v} →
    ValueTraceAgreement world-agreement (Ω ++ Ξ) V v →
    ValueTraceAgreement world-agreement (Ω ++ X ∷ Ξ) V
      (N.renameᵗᵐ (insert-seal-renaming Ω) v)
  value-trace-insert-abstract {Ω = Ω} {Ξ = Ξ} {X = X}
      (closure-trace-agrees
        {M = M} {M′ = M′} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-raw reification no-body-bullet) =
    closure-trace-agrees
      (type-environment-trace-insert-abstract θ-agrees)
      (environment-trace-insert-abstract γ-agrees)
      no-raw
      (trans
        (cong (N.renameᵗᵐ (insert-seal-renaming Ω)) reification)
        (trans
          (sym
            (substˣᵐ-renameᵗᵐ
              (insert-seal-renaming Ω)
              (N.extˢˣ
                (environmentSubstitution
                  (rename-environment (insert-seal-renaming Ω) vs)))
              (N.extˢˣ (environmentSubstitution vs))
              (N.renameᵗᵐ τ M)
              (extended-environment-substitution-rename
                (insert-seal-renaming Ω) vs)))
          (cong
            (N.substˣᵐ
              (N.extˢˣ
                (environmentSubstitution
                  (rename-environment (insert-seal-renaming Ω) vs))))
            (renameᵗᵐ-compose τ (insert-seal-renaming Ω) M))))
      (renameᵗᵐ-preserves-No•
        (insert-seal-renaming Ω) no-body-bullet)
  value-trace-insert-abstract constant-trace-agrees =
    constant-trace-agrees
  value-trace-insert-abstract
      {world-agreement = world-agreement} {Ω = Ω} {Ξ = Ξ} {X = X}
      (tagged-trace-agrees
        {G = G} {gG = gG} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement world-agreement (Ω ++ X ∷ Ξ)
        (Interpreter.tagged gG θ V))
      (cong
        (λ c → N.renameᵗᵐ (insert-seal-renaming Ω) v N.⟨ c ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ω)
            (Coercions._! G))))
      (tagged-trace-agrees
        (type-environment-trace-insert-abstract θ-agrees)
        (value-trace-insert-abstract V-agrees))
  value-trace-insert-abstract
      {W = W} {Ω = Ω} {Ξ = Ξ} {X = X}
      (sealed-trace-agrees {X = Y} name-eq V-agrees) =
    sealed-trace-agrees
      (lookup-after-abstract-insertion
        Ω Ξ {W = W} {X = X} {i = Y} name-eq)
      (value-trace-insert-abstract V-agrees)
  value-trace-insert-abstract
      {world-agreement = world-agreement} {Ω = Ω} {Ξ = Ξ} {X = X}
      (function-proxy-trace-agrees
        {p = p} {q = q} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement world-agreement (Ω ++ X ∷ Ξ)
        (Interpreter.function-proxy p q θ V))
      (cong
        (λ c → N.renameᵗᵐ (insert-seal-renaming Ω) v N.⟨ c ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ω)
            (Coercions._↦_ p q))))
      (function-proxy-trace-agrees
        (type-environment-trace-insert-abstract θ-agrees)
        (value-trace-insert-abstract V-agrees))
  value-trace-insert-abstract {Ω = Ω} {Ξ = Ξ} {X = X}
      (type-abstraction-trace-agrees
        {P = P} {raw = raw} {τ = τ} {vs = vs}
        fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
    type-abstraction-trace-agrees fresh graph
      (type-environment-trace-insert-abstract θ-agrees)
      (environment-trace-insert-abstract γ-agrees)
      no-raw
      (trans
        (cong (N.renameᵗᵐ (insert-seal-renaming Ω)) reification)
        (trans
          (sym
            (substˣᵐ-renameᵗᵐ
              (insert-seal-renaming Ω)
              (environmentSubstitution
                (rename-environment (insert-seal-renaming Ω) vs))
              (environmentSubstitution vs)
              (N.renameᵗᵐ τ (N.Λ raw))
              (environment-substitution-rename
                (insert-seal-renaming Ω) vs)))
          (cong
            (N.substˣᵐ
              (environmentSubstitution
                (rename-environment (insert-seal-renaming Ω) vs)))
            (renameᵗᵐ-compose τ (insert-seal-renaming Ω)
              (N.Λ raw)))))
      (renameᵗᵐ-preserves-Value (insert-seal-renaming Ω) vP)
      (renameᵗᵐ-preserves-No• (insert-seal-renaming Ω) no-P)
  value-trace-insert-abstract
      {world-agreement = world-agreement} {Ω = Ω} {Ξ = Ξ} {X = X}
      (forall-proxy-trace-agrees
        {c = c} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement world-agreement (Ω ++ X ∷ Ξ)
        (Interpreter.forall-proxy c θ V))
      (cong
        (λ d → N.renameᵗᵐ (insert-seal-renaming Ω) v N.⟨ d ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ω)
            (Coercions.`∀ c))))
      (forall-proxy-trace-agrees
        (type-environment-trace-insert-abstract θ-agrees)
        (value-trace-insert-abstract V-agrees))
  value-trace-insert-abstract
      {world-agreement = world-agreement} {Ω = Ω} {Ξ = Ξ} {X = X}
      (generalized-trace-agrees
        {A = A} {c = c} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement world-agreement (Ω ++ X ∷ Ξ)
        (Interpreter.generalized A c θ V))
      (cong
        (λ d → N.renameᵗᵐ (insert-seal-renaming Ω) v N.⟨ d ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ω)
            (Coercions.gen A c))))
      (generalized-trace-agrees
        (type-environment-trace-insert-abstract θ-agrees)
        (value-trace-insert-abstract V-agrees))

  environment-trace-insert-abstract :
    ∀ {W χs}
      {world-agreement : WorldTraceAgreement W χs}
      {Ω Ξ X γ vs} →
    EnvironmentTraceAgreement world-agreement (Ω ++ Ξ) γ vs →
    EnvironmentTraceAgreement world-agreement (Ω ++ X ∷ Ξ) γ
      (rename-environment (insert-seal-renaming Ω) vs)
  environment-trace-insert-abstract environment-empty-trace-agrees =
    environment-empty-trace-agrees
  environment-trace-insert-abstract
      (environment-cons-trace-agrees V-agrees γ-agrees) =
    environment-cons-trace-agrees
      (value-trace-insert-abstract V-agrees)
      (environment-trace-insert-abstract γ-agrees)

type-environment-trace-under-binder :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ X θ τ} →
  TypeEnvironmentTraceAgreement world-agreement Ξ θ τ →
  TypeEnvironmentTraceAgreement world-agreement (X ∷ Ξ)
    (abstract-name X ∷ θ) (extᵗ τ)
type-environment-trace-under-binder
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement
    (λ { {X = zero} refl → refl
       ; {X = suc Y} θ-lookup →
           lookup-agrees θ-lookup
       })

environment-trace-under-binder :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ X γ vs} →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  EnvironmentTraceAgreement world-agreement (X ∷ Ξ) γ
    (rename-environment suc vs)
environment-trace-under-binder =
  environment-trace-insert-abstract {Ω = []}
