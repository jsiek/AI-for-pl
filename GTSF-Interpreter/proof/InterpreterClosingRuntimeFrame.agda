module proof.InterpreterClosingRuntimeFrame where

-- File Charter:
--   * Reconstructs persistent runtime frames below paired and source-only
--     type-abstraction instantiation.
--   * Transports lifted static stores and records the freshly allocated
--     runtime seal names without evaluating any term.
--   * Contains no interpreter call or reduction semantics.

open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (suc; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)

open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Runtime.InterpreterRuntimeFrame as Frame
open import Typing.InterpreterSemanticTypingCore using (RuntimeContext)
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentClosing
open import Narrowing.InterpreterWorldNarrowing using
  (TypeEnvironmentScoped; allocated; seal-scoped)
import NuTermImprecision as NTI
open import proof.InterpreterInstantiationStore
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-closing-runtime-frame :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ C C′ σ σ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  (C~C′ : InterpreterTypeNarrowing C C′) →
  (σ~σ′ : TypeEnvironmentNarrowing S σ σ′) →
  NTI.LiftStoreⁱ
    ((Data.Nat.zero ˣ⊑ˣ Data.Nat.zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Frame.RuntimeFrameNarrowing
    (allocate-both S C~C′ σ~σ′)
    ((Data.Nat.zero ˣ⊑ˣ Data.Nat.zero) ∷ ⇑ᵢ Φ)
    (suc Δᴸ) (suc Δᴿ) ρ′
    (seal-name (freshSealName U) ∷ θ)
    (seal-name (freshSealName U′) ∷ θ′)
paired-closing-runtime-frame
    {U = U} {U′} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ′ = ρ′} {θ = θ} {θ′}
    {C = C} {C′} {σ} {σ′}
    runtime R≤S C~C′ σ~σ′ liftρ =
  Frame.runtime-frame-narrowing
    left-context
    right-context
    (paired-lift-store-correspondence-realization
      liftρ (Frame.store-correspondences-realized allocated-runtime))
    (paired-seal-allocation-realization
      R≤S C~C′ σ~σ′
      (Frame.type-environments-realized runtime))
    (s≤s (Frame.abstract-supply runtime))
  where
  allocated-runtime =
    Frame.runtime-frame-weaken (extension-both R≤S) runtime

  left-context =
    subst
      (λ Σ →
        RuntimeContext (allocate U C σ) (suc Δᴸ) Σ
          (seal-name (freshSealName U) ∷ θ))
      (sym (NTI.leftStoreⁱ-lift liftρ))
      (SemanticProof.runtime-context-name
        (seal-scoped (allocated (here refl)))
        (Frame.left-runtime-context allocated-runtime))

  right-context =
    subst
      (λ Σ →
        RuntimeContext (allocate U′ C′ σ′) (suc Δᴿ) Σ
          (seal-name (freshSealName U′) ∷ θ′))
      (sym (NTI.rightStoreⁱ-lift liftρ))
      (SemanticProof.runtime-context-name
        (seal-scoped (allocated (here refl)))
        (Frame.right-runtime-context allocated-runtime))

left-closing-runtime-frame :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ C σ}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  Frame.RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  (σ-ok : TypeEnvironmentScoped U σ) →
  NTI.LiftLeftStoreⁱ
    ((Data.Nat.zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Frame.RuntimeFrameNarrowing
    (allocate-left-dynamic {A = C} S σ-ok)
    ((Data.Nat.zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    (suc Δᴸ) Δᴿ ρ′
    (seal-name (freshSealName U) ∷ θ) θ′
left-closing-runtime-frame
    {U = U} {U′} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {ρ′ = ρ′} {θ = θ} {θ′} {C = C} {σ}
    runtime R≤S σ-ok liftρ =
  Frame.runtime-frame-narrowing
    left-context
    right-context
    (left-lift-store-correspondence-realization
      liftρ (Frame.store-correspondences-realized allocated-runtime))
    (left-dynamic-seal-allocation-realization-at
      R≤S σ-ok (Frame.type-environments-realized runtime))
    (≤-trans (Frame.abstract-supply runtime)
      (n≤1+n (nextAbstractIndex θ)))
  where
  allocated-runtime =
    Frame.runtime-frame-weaken
      (extension-left {A = C} R≤S) runtime

  left-context =
    subst
      (λ Σ →
        RuntimeContext (allocate U C σ) (suc Δᴸ) Σ
          (seal-name (freshSealName U) ∷ θ))
      (sym (NTI.leftStoreⁱ-lift-left liftρ))
      (SemanticProof.runtime-context-name
        (seal-scoped (allocated (here refl)))
        (Frame.left-runtime-context allocated-runtime))

  right-context =
    subst
      (λ Σ → RuntimeContext U′ Δᴿ Σ θ′)
      (sym (NTI.rightStoreⁱ-lift-left liftρ))
      (Frame.right-runtime-context allocated-runtime)
