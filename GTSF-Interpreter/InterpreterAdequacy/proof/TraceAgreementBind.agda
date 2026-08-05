module InterpreterAdequacy.proof.TraceAgreementBind where

-- File Charter:
--   * Reindexes trace agreements across one fresh small-step store binding.
--   * Inserts the new de Bruijn seal after any enclosing abstract names and
--     shifts reified environments, values, terms, and coercions coherently.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

open import Coercions using (renameᶜ)
open import Interpreter using
  ( Name
  ; TypeEnvironment
  ; Value
  ; allocation
  ; allocate
  ; freshSealName
  ; world
  ; seal-name
  ; abstract-name
  ; lookup
  )
open import InterpreterAdequacy.TraceAgreement
open import NuReduction using (bind)
import NuTerms as N
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-compose)
open import proof.Core.Properties.NuTermProperties using
  ( renameˣ-renameᵗᵐ
  ; renameᵗᵐ-compose
  ; renameᵗᵐ-preserves-Value
  ; renameᵗᵐ-preserves-No•
  )
open import proof.Substitution.Term.TermSubstitutionSyntax using
  (substˣᵐ-renameᵗᵐ)
open import Types using (Renameᵗ; extᵗ)

-- Insert the newly allocated seal immediately after the abstract names bound
-- by the surrounding syntactic `Λ`s.
insert-seal-renaming : List Name → Renameᵗ
insert-seal-renaming [] = suc
insert-seal-renaming (X ∷ Ξ) = extᵗ (insert-seal-renaming Ξ)

lookup-after-seal-insertion :
  ∀ Ξ {cells X a next A θ} →
  lookup (visibleTypeNames Ξ (world next cells)) X ≡ just a →
  lookup
    (visibleTypeNames Ξ
      (world (suc next)
        (allocation (Interpreter.seal-name-id next) A θ ∷ cells)))
    (insert-seal-renaming Ξ X) ≡ just a
lookup-after-seal-insertion [] old-lookup = old-lookup
lookup-after-seal-insertion (Y ∷ Ξ) {X = zero} old-lookup = old-lookup
lookup-after-seal-insertion
    (Y ∷ Ξ) {cells = cells} {X = suc X} {a = a}
    {next = next} {A = A} {θ = θ} old-lookup =
  lookup-after-seal-insertion
    Ξ {cells = cells} {X = X} {a = a}
    {next = next} {A = A} {θ = θ} old-lookup

new-seal-lookup :
  ∀ Ξ {next cells A θ} →
  lookup
    (visibleTypeNames Ξ
      (world (suc next)
        (allocation (Interpreter.seal-name-id next) A θ ∷ cells)))
    (Data.List.length Ξ) ≡
    just (seal-name (Interpreter.seal-name-id next))
new-seal-lookup [] = refl
new-seal-lookup
    (X ∷ Ξ) {next = next} {cells = cells} {A = A} {θ = θ} =
  new-seal-lookup Ξ {next = next} {cells = cells} {A = A} {θ = θ}

newest-allocation-lookup :
  ∀ {W A θ} →
  lookup (visibleTypeNames [] (allocate W A θ)) zero ≡
    just (seal-name (freshSealName W))
newest-allocation-lookup {W = world next cells} = refl

rename-environment : Renameᵗ → List N.Term → List N.Term
rename-environment ρ = map (N.renameᵗᵐ ρ)

environment-substitution-rename :
  ∀ ρ vs x →
  environmentSubstitution (rename-environment ρ vs) x ≡
    N.renameᵗᵐ ρ (environmentSubstitution vs x)
environment-substitution-rename ρ [] x = refl
environment-substitution-rename ρ (v ∷ vs) zero = refl
environment-substitution-rename ρ (v ∷ vs) (suc x) =
  environment-substitution-rename ρ vs x

extended-environment-substitution-rename :
  ∀ ρ vs x →
  N.extˢˣ (environmentSubstitution (rename-environment ρ vs)) x ≡
    N.renameᵗᵐ ρ (N.extˢˣ (environmentSubstitution vs) x)
extended-environment-substitution-rename ρ vs zero = refl
extended-environment-substitution-rename ρ vs (suc x) =
  trans
    (cong (N.renameˣᵐ suc)
      (environment-substitution-rename ρ vs x))
    (renameˣ-renameᵗᵐ suc ρ (environmentSubstitution vs x))

type-environment-trace-bind :
  ∀ {next cells χs A B allocation-θ}
    {old-agreement :
      WorldTraceAgreement (world next cells) χs}
    {new-agreement :
      WorldTraceAgreement
        (world (suc next)
          (allocation (Interpreter.seal-name-id next) A
            allocation-θ ∷ cells))
        (χs ++ bind B ∷ [])}
    {Ξ θ τ} →
  TypeEnvironmentTraceAgreement old-agreement Ξ θ τ →
  TypeEnvironmentTraceAgreement new-agreement Ξ θ
    (λ X → insert-seal-renaming Ξ (τ X))
type-environment-trace-bind
    {next = next} {cells = cells} {A = A}
    {allocation-θ = allocation-θ} {Ξ = Ξ} {τ = τ}
    (type-environment-trace-agreement lookup-agrees) =
  type-environment-trace-agreement
    (λ {X = X} {a = a} θ-lookup →
      lookup-after-seal-insertion
        Ξ {cells = cells} {X = τ X} {a = a}
        {next = next} {A = A} {θ = allocation-θ}
        (lookup-agrees θ-lookup))

mutual
  value-trace-bind :
    ∀ {next cells χs A B allocation-θ}
      {old-agreement :
        WorldTraceAgreement (world next cells) χs}
      {new-agreement :
        WorldTraceAgreement
          (world (suc next)
            (allocation
              (Interpreter.seal-name-id next) A allocation-θ ∷ cells))
          (χs ++ bind B ∷ [])}
      {Ξ V v} →
    ValueTraceAgreement old-agreement Ξ V v →
    ValueTraceAgreement new-agreement Ξ V
      (N.renameᵗᵐ (insert-seal-renaming Ξ) v)
  value-trace-bind
      {Ξ = Ξ}
      (closure-trace-agrees
        {M = M} {M′ = M′} {τ = τ} {vs = vs}
        θ-agrees γ-agrees no-raw reification no-body-bullet) =
    closure-trace-agrees
      (type-environment-trace-bind θ-agrees)
      (environment-trace-bind γ-agrees)
      no-raw
      (trans
        (cong (N.renameᵗᵐ (insert-seal-renaming Ξ)) reification)
        (trans
          (sym
            (substˣᵐ-renameᵗᵐ
              (insert-seal-renaming Ξ)
              (N.extˢˣ
                (environmentSubstitution
                  (rename-environment (insert-seal-renaming Ξ) vs)))
              (N.extˢˣ (environmentSubstitution vs))
              (N.renameᵗᵐ τ M)
              (extended-environment-substitution-rename
                (insert-seal-renaming Ξ) vs)))
          (cong
            (N.substˣᵐ
              (N.extˢˣ
                (environmentSubstitution
                  (rename-environment (insert-seal-renaming Ξ) vs))))
            (renameᵗᵐ-compose τ (insert-seal-renaming Ξ) M))))
      (renameᵗᵐ-preserves-No• (insert-seal-renaming Ξ) no-body-bullet)
  value-trace-bind constant-trace-agrees =
    constant-trace-agrees
  value-trace-bind
      {new-agreement = new-agreement} {Ξ = Ξ}
      (tagged-trace-agrees
        {G = G} {gG = gG} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement new-agreement Ξ
        (Interpreter.tagged gG θ V))
      (cong
        (λ c → N.renameᵗᵐ (insert-seal-renaming Ξ) v N.⟨ c ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ξ)
            (Coercions._! G))))
      (tagged-trace-agrees
        (type-environment-trace-bind θ-agrees)
        (value-trace-bind V-agrees))
  value-trace-bind
      {next = next} {cells = cells} {A = allocation-A}
      {allocation-θ = allocation-θ} {Ξ = Ξ}
      (sealed-trace-agrees {A = A} {X = X} name-eq V-agrees) =
    sealed-trace-agrees
      (lookup-after-seal-insertion
        Ξ {cells = cells} {X = X} {next = next}
        {A = allocation-A} {θ = allocation-θ} name-eq)
      (value-trace-bind V-agrees)
  value-trace-bind
      {new-agreement = new-agreement} {Ξ = Ξ}
      (function-proxy-trace-agrees
        {p = p} {q = q} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement new-agreement Ξ
        (Interpreter.function-proxy p q θ V))
      (cong
        (λ c → N.renameᵗᵐ (insert-seal-renaming Ξ) v N.⟨ c ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ξ)
            (Coercions._↦_ p q))))
      (function-proxy-trace-agrees
        (type-environment-trace-bind θ-agrees)
        (value-trace-bind V-agrees))
  value-trace-bind {Ξ = Ξ}
      (type-abstraction-trace-agrees
        {P = P} {raw = raw} {τ = τ} {vs = vs}
        fresh graph θ-agrees γ-agrees no-raw reification vP no-P) =
    type-abstraction-trace-agrees fresh graph
      (type-environment-trace-bind θ-agrees)
      (environment-trace-bind γ-agrees)
      no-raw
      (trans
        (cong (N.renameᵗᵐ (insert-seal-renaming Ξ)) reification)
        (trans
          (sym
            (substˣᵐ-renameᵗᵐ
              (insert-seal-renaming Ξ)
              (environmentSubstitution
                (rename-environment (insert-seal-renaming Ξ) vs))
              (environmentSubstitution vs)
              (N.renameᵗᵐ τ (N.Λ raw))
              (environment-substitution-rename
                (insert-seal-renaming Ξ) vs)))
          (cong
            (N.substˣᵐ
              (environmentSubstitution
                (rename-environment (insert-seal-renaming Ξ) vs)))
            (renameᵗᵐ-compose τ (insert-seal-renaming Ξ)
              (N.Λ raw)))))
      (renameᵗᵐ-preserves-Value (insert-seal-renaming Ξ) vP)
      (renameᵗᵐ-preserves-No• (insert-seal-renaming Ξ) no-P)
  value-trace-bind
      {new-agreement = new-agreement} {Ξ = Ξ}
      (forall-proxy-trace-agrees
        {c = c} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement new-agreement Ξ
        (Interpreter.forall-proxy c θ V))
      (cong
        (λ d → N.renameᵗᵐ (insert-seal-renaming Ξ) v N.⟨ d ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ξ)
            (Coercions.`∀ c))))
      (forall-proxy-trace-agrees
        (type-environment-trace-bind θ-agrees)
        (value-trace-bind V-agrees))
  value-trace-bind
      {new-agreement = new-agreement} {Ξ = Ξ}
      (generalized-trace-agrees
        {A = A} {c = c} {θ = θ} {τ = τ} {V = V} {v = v}
        θ-agrees V-agrees) =
    subst
      (ValueTraceAgreement new-agreement Ξ
        (Interpreter.generalized A c θ V))
      (cong
        (λ d → N.renameᵗᵐ (insert-seal-renaming Ξ) v N.⟨ d ⟩)
        (sym
          (renameᶜ-compose τ (insert-seal-renaming Ξ)
            (Coercions.gen A c))))
      (generalized-trace-agrees
        (type-environment-trace-bind θ-agrees)
        (value-trace-bind V-agrees))

  environment-trace-bind :
    ∀ {next cells χs A B allocation-θ}
      {old-agreement :
        WorldTraceAgreement (world next cells) χs}
      {new-agreement :
        WorldTraceAgreement
          (world (suc next)
            (allocation
              (Interpreter.seal-name-id next) A allocation-θ ∷ cells))
          (χs ++ bind B ∷ [])}
      {Ξ γ vs} →
    EnvironmentTraceAgreement old-agreement Ξ γ vs →
    EnvironmentTraceAgreement new-agreement Ξ γ
      (rename-environment (insert-seal-renaming Ξ) vs)
  environment-trace-bind environment-empty-trace-agrees =
    environment-empty-trace-agrees
  environment-trace-bind
      (environment-cons-trace-agrees V-agrees γ-agrees) =
    environment-cons-trace-agrees
      (value-trace-bind V-agrees)
      (environment-trace-bind γ-agrees)
