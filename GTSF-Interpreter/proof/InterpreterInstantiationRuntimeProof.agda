module proof.InterpreterInstantiationRuntimeProof where

-- File Charter:
--   * Constructs the synchronized runtime after paired or source-only `ν`
--     allocation.
--   * Transports unary runtime contexts across static binder-lift equations
--     and realizes both the new store head and every shifted old link.
--   * Uses no interpreter execution or reduction semantics.

open import Agda.Builtin.Equality using (refl)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym)

open import ImprecisionWf using
  (_ˣ⊑★; _ˣ⊑ˣ_; ⇑ᵢ; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing; type-narrowing)
open import Typing.InterpreterSemanticTypingCore using
  (RuntimeContext; WorldTyping; allocate-world-typed)
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentClosing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing using (TypeEnvironmentScoped)
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  ( assumption-membership-unique-matched
  ; assumption-membership-unique-source
  )
open import proof.InterpreterInstantiationStore
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds

paired-instantiation-runtime :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ A A′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  WorldTyping U →
  WorldTyping U′ →
  WfTy Δᴸ A →
  WfTy Δᴿ A′ →
  (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) →
  (p⇑ :
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ∣ suc Δᴸ
      ⊢ ⇑ᵗ A ⊑ ⇑ᵗ A′ ⊣ suc Δᴿ) →
  NTI.LiftStoreⁱ
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ′ →
  Σ[ θ~θ′ ∈ TypeEnvironmentNarrowing S θ θ′ ]
    RuntimeNarrowing
      (allocate-both S (type-narrowing p) θ~θ′)
      ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)
      (NTI.store-matched zero (⇑ᵗ A)
        zero (⇑ᵗ A′) p⇑ ∷ ρ′)
      (seal-name (freshSealName U) ∷ θ)
      (seal-name (freshSealName U′) ∷ θ′)
paired-instantiation-runtime
    {U = U} {U′} {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ′}
    {θ} {θ′} {A} {A′}
    runtime R≤S U⊢ U′⊢ hA hA′ p p⇑ liftρ
    with type-environment-realization-weaken R≤S
      (type-environments-realized runtime)
paired-instantiation-runtime
    {U = U} {U′} {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ′}
    {θ} {θ′} {A} {A′}
    runtime R≤S U⊢ U′⊢ hA hA′ p p⇑ liftρ
    | weakened-types =
  environments-narrow weakened-types ,
  runtime-narrowing
    (assumption-membership-unique-matched
      (assumption-membership-unique runtime))
    (allocate-world-typed U⊢
      (left-runtime-context weakened-runtime) hA)
    (allocate-world-typed U′⊢
      (right-runtime-context weakened-runtime) hA′)
    left-context
    right-context
    (runtime-type-seal (right-runtime-environment runtime))
    new-store-realization
    (paired-seal-allocation-realization
      R≤S (type-narrowing p)
      (environments-narrow weakened-types)
      (type-environments-realized runtime))
    (s≤s (abstract-supply runtime))
  where
  weakened-runtime =
    runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime

  left-context =
    subst
      (λ Σ →
        RuntimeContext
          (allocate U A θ) (suc Δᴸ) Σ
          (seal-name (freshSealName U) ∷ θ))
      (sym (cong ((zero , ⇑ᵗ A) ∷_)
        (NTI.leftStoreⁱ-lift liftρ)))
      (SemanticProof.runtime-context-seal
        (left-runtime-context weakened-runtime))

  right-context =
    subst
      (λ Σ →
        RuntimeContext
          (allocate U′ A′ θ′) (suc Δᴿ) Σ
          (seal-name (freshSealName U′) ∷ θ′))
      (sym (cong ((zero , ⇑ᵗ A′) ∷_)
        (NTI.rightStoreⁱ-lift liftρ)))
      (SemanticProof.runtime-context-seal
        (right-runtime-context weakened-runtime))

  lifted-store-realization =
    paired-lift-store-correspondence-realization
      liftρ
      (store-correspondence-realization-weaken
        (extension-both R≤S)
        (store-correspondences-realized runtime))

  new-store-realization =
    store-correspondence-realization
      λ
        { (NTI.correspondence-stored (here refl)) →
            freshSealName U , freshSealName U′ ,
            refl , refl , link-here
        ; (NTI.correspondence-stored (there member)) →
            realizes-store-correspondence
              lifted-store-realization
              (NTI.correspondence-stored member)
        ; (NTI.correspondence-linked (there member)) →
            realizes-store-correspondence
              lifted-store-realization
              (NTI.correspondence-linked member)
        }

left-instantiation-runtime :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ ρ′ θ θ′ A}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  RuntimeNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  (R≤S : WorldExtension R S) →
  WorldTyping U →
  WorldTyping U′ →
  WfTy Δᴸ A →
  (hA⇑ : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  NTI.LiftLeftStoreⁱ
    ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  Σ[ θ-ok ∈ TypeEnvironmentScoped U θ ]
    RuntimeNarrowing
      (allocate-left-dynamic {A = A} S θ-ok)
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      (suc Δᴸ) Δᴿ
      (NTI.store-left zero (⇑ᵗ A) hA⇑ ∷ ρ′)
      (seal-name (freshSealName U) ∷ θ) θ′
left-instantiation-runtime
    {U = U} {U′} {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ′}
    {θ} {θ′} {A}
    runtime R≤S U⊢ U′⊢ hA hA⇑ liftρ
    with left-dynamic-seal-allocation-realization
      {allocated-type = A}
      R≤S (type-environments-realized runtime)
left-instantiation-runtime
    {U = U} {U′} {Φ} {Δᴸ} {Δᴿ} {ρ} {ρ′}
    {θ} {θ′} {A}
    runtime R≤S U⊢ U′⊢ hA hA⇑ liftρ
    | θ-ok , allocated-types =
  θ-ok ,
  runtime-narrowing
    (assumption-membership-unique-source
      (assumption-membership-unique runtime))
    (allocate-world-typed U⊢
      (left-runtime-context weakened-runtime) hA)
    U′⊢
    left-context
    right-context
    (right-runtime-environment runtime)
    new-store-realization
    allocated-types
    (≤-trans (abstract-supply runtime)
      (n≤1+n (nextAbstractIndex θ)))
  where
  weakened-runtime =
    runtime-narrowing-weaken R≤S U⊢ U′⊢ runtime

  left-context =
    subst
      (λ Σ →
        RuntimeContext
          (allocate U A θ) (suc Δᴸ) Σ
          (seal-name (freshSealName U) ∷ θ))
      (sym (cong ((zero , ⇑ᵗ A) ∷_)
        (NTI.leftStoreⁱ-lift-left liftρ)))
      (SemanticProof.runtime-context-seal
        (left-runtime-context weakened-runtime))

  right-context =
    subst
      (λ Σ → RuntimeContext U′ Δᴿ Σ θ′)
      (sym (NTI.rightStoreⁱ-lift-left liftρ))
      (right-runtime-context weakened-runtime)

  lifted-store-realization =
    left-lift-store-correspondence-realization
      liftρ
      (store-correspondence-realization-weaken
        (extension-left {A = A} R≤S)
        (store-correspondences-realized runtime))

  new-store-realization =
    store-correspondence-realization
      λ
        { (NTI.correspondence-stored (there member)) →
            realizes-store-correspondence
              lifted-store-realization
              (NTI.correspondence-stored member)
        ; (NTI.correspondence-linked (there member)) →
            realizes-store-correspondence
              lifted-store-realization
              (NTI.correspondence-linked member)
        }
