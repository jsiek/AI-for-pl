module InterpreterAdequacy.proof.SyntaxReification where

-- File Charter:
--   * Provides syntax-only facts about the substitutions used to reify
--     interpreter environments.
--   * Relates successful semantic lookup to the corresponding syntactic
--     value and proves that reification preserves the no-bullet invariant.
--   * Contains no interpreter recursion and constructs no reduction step.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

open import Interpreter using (Environment; Value; lookup)
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.TraceAgreementProperties using
  (value-trace-no-bullet)
import NuTerms as N
open import proof.Core.Properties.NuTermProperties using
  (renameˣᵐ-preserves-No•; renameᵗᵐ-preserves-No•)
open import Types using (Renameᵗ)

lookup-environment-trace :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ γ vs x V} →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  lookup γ x ≡ just V →
  ∃[ v ]
    (environmentSubstitution vs x ≡ v) ×
    ValueTraceAgreement world-agreement Ξ V v
lookup-environment-trace environment-empty-trace-agrees ()
lookup-environment-trace
    {x = zero}
    (environment-cons-trace-agrees V-agrees γ-agrees)
    refl =
  _ , refl , V-agrees
lookup-environment-trace
    {x = suc x}
    (environment-cons-trace-agrees V-agrees γ-agrees)
    lookup-eq =
  lookup-environment-trace γ-agrees lookup-eq

SubstitutionNoBullet : N.Substˣ → Set
SubstitutionNoBullet σ = ∀ x → N.No• (σ x)

substˣᵐ-cong :
  ∀ {σ τ} →
  (∀ x → σ x ≡ τ x) →
  ∀ M → N.substˣᵐ σ M ≡ N.substˣᵐ τ M
substˣᵐ-cong env-eq (N.` x) = env-eq x
substˣᵐ-cong env-eq (N.ƛ M) =
  cong N.ƛ_ (substˣᵐ-cong ext-eq M)
  where
  ext-eq : ∀ x → N.extˢˣ _ x ≡ N.extˢˣ _ x
  ext-eq zero = refl
  ext-eq (suc x) = cong (N.renameˣᵐ suc) (env-eq x)
substˣᵐ-cong env-eq (L N.· M) =
  cong₂ N._·_ (substˣᵐ-cong env-eq L) (substˣᵐ-cong env-eq M)
substˣᵐ-cong {σ = σ} {τ = τ} env-eq (N.Λ M) =
  cong N.Λ_ (substˣᵐ-cong lift-eq M)
  where
  lift-eq : ∀ x → N.↑ᵗᵐ σ x ≡ N.↑ᵗᵐ τ x
  lift-eq x = cong (N.renameᵗᵐ suc) (env-eq x)
substˣᵐ-cong env-eq (M N.•) =
  cong N._• (substˣᵐ-cong env-eq M)
substˣᵐ-cong env-eq (N.ν A L c) =
  cong (λ L′ → N.ν A L′ c) (substˣᵐ-cong env-eq L)
substˣᵐ-cong env-eq (N.$ κ) = refl
substˣᵐ-cong env-eq (L N.⊕[ op ] M) =
  cong₂ N._⊕[ op ]_
    (substˣᵐ-cong env-eq L) (substˣᵐ-cong env-eq M)
substˣᵐ-cong env-eq (M N.⟨ c ⟩) =
  cong (λ M′ → M′ N.⟨ c ⟩) (substˣᵐ-cong env-eq M)
substˣᵐ-cong env-eq N.blame = refl

environment-substitution-no-bullet :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ γ vs} →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  SubstitutionNoBullet (environmentSubstitution vs)
environment-substitution-no-bullet environment-empty-trace-agrees x =
  N.no•-`
environment-substitution-no-bullet
    (environment-cons-trace-agrees V-agrees γ-agrees) zero =
  value-trace-no-bullet V-agrees
environment-substitution-no-bullet
    (environment-cons-trace-agrees V-agrees γ-agrees) (suc x) =
  environment-substitution-no-bullet γ-agrees x

substitution-no-bullet-ext :
  ∀ {σ} →
  SubstitutionNoBullet σ →
  SubstitutionNoBullet (N.extˢˣ σ)
substitution-no-bullet-ext no-σ zero = N.no•-`
substitution-no-bullet-ext no-σ (suc x) =
  renameˣᵐ-preserves-No• suc (no-σ x)

substitution-no-bullet-type-lift :
  ∀ {σ} →
  SubstitutionNoBullet σ →
  SubstitutionNoBullet (N.↑ᵗᵐ σ)
substitution-no-bullet-type-lift no-σ x =
  renameᵗᵐ-preserves-No• suc (no-σ x)

substˣᵐ-preserves-No• :
  ∀ {σ M} →
  SubstitutionNoBullet σ →
  N.No• M →
  N.No• (N.substˣᵐ σ M)
substˣᵐ-preserves-No• no-σ N.no•-` = no-σ _
substˣᵐ-preserves-No• no-σ (N.no•-ƛ no-M) =
  N.no•-ƛ
    (substˣᵐ-preserves-No• (substitution-no-bullet-ext no-σ) no-M)
substˣᵐ-preserves-No• no-σ (N.no•-· no-L no-M) =
  N.no•-·
    (substˣᵐ-preserves-No• no-σ no-L)
    (substˣᵐ-preserves-No• no-σ no-M)
substˣᵐ-preserves-No• no-σ (N.no•-Λ no-M) =
  N.no•-Λ
    (substˣᵐ-preserves-No•
      (substitution-no-bullet-type-lift no-σ) no-M)
substˣᵐ-preserves-No• no-σ (N.no•-ν no-M) =
  N.no•-ν (substˣᵐ-preserves-No• no-σ no-M)
substˣᵐ-preserves-No• no-σ N.no•-$ = N.no•-$
substˣᵐ-preserves-No• no-σ (N.no•-⊕ no-L no-M) =
  N.no•-⊕
    (substˣᵐ-preserves-No• no-σ no-L)
    (substˣᵐ-preserves-No• no-σ no-M)
substˣᵐ-preserves-No• no-σ (N.no•-⟨⟩ no-M) =
  N.no•-⟨⟩ (substˣᵐ-preserves-No• no-σ no-M)
substˣᵐ-preserves-No• no-σ N.no•-blame = N.no•-blame

reified-term :
  Renameᵗ → List N.Term → N.Term → N.Term
reified-term τ vs M =
  N.substˣᵐ (environmentSubstitution vs) (N.renameᵗᵐ τ M)

reified-term-no-bullet :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ γ vs τ M} →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  N.No• M →
  N.No• (reified-term τ vs M)
reified-term-no-bullet γ-agrees no-M =
  substˣᵐ-preserves-No•
    (environment-substitution-no-bullet γ-agrees)
    (renameᵗᵐ-preserves-No• _ no-M)

reified-body-no-bullet :
  ∀ {W χs}
    {world-agreement : WorldTraceAgreement W χs}
    {Ξ γ vs τ M} →
  EnvironmentTraceAgreement world-agreement Ξ γ vs →
  N.No• M →
  N.No•
    (N.substˣᵐ (N.extˢˣ (environmentSubstitution vs))
      (N.renameᵗᵐ τ M))
reified-body-no-bullet γ-agrees no-M =
  substˣᵐ-preserves-No•
    (substitution-no-bullet-ext
      (environment-substitution-no-bullet γ-agrees))
    (renameᵗᵐ-preserves-No• _ no-M)
