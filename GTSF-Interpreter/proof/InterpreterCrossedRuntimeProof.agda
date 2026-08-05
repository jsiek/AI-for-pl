module proof.InterpreterCrossedRuntimeProof where

-- File Charter:
--   * Constructs the exact synchronized runtime produced by two sibling
--     dynamic instantiations whose fresh seals are related crosswise.
--   * Realizes the swapped universal context and both crossed store links.
--   * Uses only interpreter world equations and static narrowing metatheory.
--   * Contains no reduction, catch-up, or DGG theorem.

open import Agda.Builtin.Equality using (refl)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (zero; suc; s≤s)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (sym)

open import ImprecisionWf using
  ( ImpAssm
  ; ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᵢₐ
  ; swapRight∀∀ᵢ
  ; id★
  )
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing; type-narrowing)
open import Runtime.InterpreterCrossedStoreLift using
  (left-store-double-lift; right-store-double-lift)
open import Typing.InterpreterSemanticTypingCore using
  ( AllocationRepresentation
  ; RuntimeContext
  ; StoreTyping
  ; TypeEnvironmentLength
  ; WorldExtension
  ; WorldTyping
  ; ⟦_⟧[_]
  ; allocation-representation
  ; allocate-world-typed
  ; length-cons
  ; runtime-context
  ; store-cons
  ; type-length
  ; type-scope
  ; store-typing
  ; world-extension-allocate
  ; world-extension-refl
  )
open import Simulation.Core.InterpreterSimulationContext
open import Simulation.Core.InterpreterSimulationContextProperties using
  ( store-correspondence-realization-weaken
  ; type-environment-realization-weaken
  )
open import Runtime.InterpreterStoreCorrespondenceRealization
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterTypeEnvironmentRealization
open import Narrowing.InterpreterWorldNarrowing using
  ( allocated
  ; seal-scoped
  ; _∷-scoped_
  )
import NuTermImprecision as NTI
open import
  proof.NuImprecisionAssumptionMembershipUniquenessProof using
  (assumption-membership-unique-swap)
open import proof.InterpreterInstantiationStore using
  (paired-lift-store-correspondence-realization)
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

open Narrowing.InterpreterTermNarrowing.RelatedWorlds


private
  dynamic-type-narrowing :
    InterpreterTypeNarrowing ★ ★
  dynamic-type-narrowing =
    type-narrowing {Φ = []} {Δᴸ = zero} {Δᴿ = zero} id★


  double-assumption-under-names :
    ∀ {W W′}
      {R : WorldRelation W W′}
      {θ θ′ name₀ name₁ name₀′ name₁′}
      {assumption : ImpAssm} →
    AssumptionRealization R θ θ′ assumption →
    AssumptionRealization R
      (name₀ ∷ name₁ ∷ θ) (name₀′ ∷ name₁′ ∷ θ′)
      (⇑ᵢₐ (⇑ᵢₐ assumption))
  double-assumption-under-names
      (paired-assumption left-at right-at name~name′) =
    paired-assumption left-at right-at name~name′
  double-assumption-under-names
      (source-dynamic-assumption left-at name-ok) =
    source-dynamic-assumption left-at name-ok


  double-assumptions-under-names :
    ∀ {W W′}
      {R : WorldRelation W W′}
      {Φ : ImpCtx}
      {θ θ′ name₀ name₁ name₀′ name₁′} →
    (∀ {assumption} →
      assumption ∈ Φ →
      AssumptionRealization R θ θ′ assumption) →
    ∀ {assumption} →
    assumption ∈ ⇑ᵢ (⇑ᵢ Φ) →
    AssumptionRealization R
      (name₀ ∷ name₁ ∷ θ) (name₀′ ∷ name₁′ ∷ θ′)
      assumption
  double-assumptions-under-names {Φ = []} realizes ()
  double-assumptions-under-names {Φ = assumption ∷ Φ}
      realizes (here refl) =
    double-assumption-under-names (realizes (here refl))
  double-assumptions-under-names {Φ = assumption ∷ Φ}
      realizes (there member) =
    double-assumptions-under-names
      (λ old-member → realizes (there old-member))
      member


crossed-type-environment-realization :
  ∀ {W W′ Φ θ θ′}
    {R : WorldRelation W W′} →
  (realization : TypeEnvironmentRealization R Φ θ θ′) →
  TypeEnvironmentRealization
    (allocate-crossed
      {A₀ = ★} {A₁ = ★} {B₀ = ★} {B₁ = ★}
      {θA₀ = θ} {θA₁ = θ} {θB₀ = θ′} {θB₁ = θ′} R
      dynamic-type-narrowing (environments-narrow realization)
      dynamic-type-narrowing (environments-narrow realization))
    (swapRight∀∀ᵢ Φ)
    (seal-name (freshSealName (allocate W ★ θ)) ∷
      seal-name (freshSealName W) ∷ θ)
    (seal-name (freshSealName (allocate W′ ★ θ′)) ∷
      seal-name (freshSealName W′) ∷ θ′)
crossed-type-environment-realization
    {W} {W′} {Φ} {θ} {θ′} {R} realization =
  type-environment-realization
    ((seal-scoped (allocated (here refl))) ∷ˡ⊑ᵗᵉ
      ((seal-name⊑ link-cross-old-new) ∷⊑∷ᵗᵉ
        ((seal-scoped (allocated (there (here refl))))
          ∷ʳ⊑ᵗᵉ (environments-narrow weakened))))
    λ
      { (here refl) →
          paired-assumption refl refl
            (seal-name⊑ link-cross-new-old)
      ; (there (here refl)) →
          paired-assumption refl refl
            (seal-name⊑ link-cross-old-new)
      ; (there (there member)) →
          double-assumptions-under-names
            (realizes-assumption weakened) member
      }
  where
  crossed =
    allocate-crossed
      {A₀ = ★} {A₁ = ★} {B₀ = ★} {B₁ = ★}
      {θA₀ = θ} {θA₁ = θ} {θB₀ = θ′} {θB₁ = θ′} R
      dynamic-type-narrowing (environments-narrow realization)
      dynamic-type-narrowing (environments-narrow realization)

  weakened :
    TypeEnvironmentRealization crossed Φ θ θ′
  weakened =
    type-environment-realization-weaken
      (extension-crossed extension-refl) realization


private
  crossed-runtime-context :
    ∀ {W Δ Σ θ} →
    WorldTyping W →
    RuntimeContext W Δ Σ θ →
    RuntimeContext
      (allocate (allocate W ★ θ) ★ θ)
      (suc (suc Δ))
      ((zero , ★) ∷ (suc zero , ★) ∷ ⟰ᵗ (⟰ᵗ Σ))
      (seal-name (freshSealName (allocate W ★ θ)) ∷
        seal-name (freshSealName W) ∷ θ)
  crossed-runtime-context {W} {Δ} {Σ} {θ} W⊢ runtime =
    runtime-context
      (length-cons (length-cons (type-length runtime)))
      ((seal-scoped (allocated (here refl))) ∷-scoped
        ((seal-scoped (allocated (there (here refl)))) ∷-scoped
          SemanticProof.scope-weaken W≤W₂ (type-scope runtime)))
      (store-cons refl outer-representation
        (store-cons refl inner-representation shifted-store))
    where
    W≤W₂ :
      Typing.InterpreterSemanticTypingCore.WorldExtension
        W (allocate (allocate W ★ θ) ★ θ)
    W≤W₂ =
      world-extension-allocate
        (world-extension-allocate world-extension-refl)

    outer-representation :
      AllocationRepresentation
        (allocate (allocate W ★ θ) ★ θ)
        (freshSealName (allocate W ★ θ))
        ⟦ ★ ⟧[
          seal-name (freshSealName (allocate W ★ θ)) ∷
          seal-name (freshSealName W) ∷ θ ]
    outer-representation =
      allocation-representation ★ θ (here refl) refl

    inner-representation :
      AllocationRepresentation
        (allocate (allocate W ★ θ) ★ θ)
        (freshSealName W)
        ⟦ ★ ⟧[
          seal-name (freshSealName (allocate W ★ θ)) ∷
          seal-name (freshSealName W) ∷ θ ]
    inner-representation =
      allocation-representation ★ θ (there (here refl)) refl

    shifted-store :
      StoreTyping
        (allocate (allocate W ★ θ) ★ θ)
        (seal-name (freshSealName (allocate W ★ θ)) ∷
          seal-name (freshSealName W) ∷ θ)
        (⟰ᵗ (⟰ᵗ Σ))
    shifted-store =
      SemanticProof.store-shift
        (seal-name (freshSealName (allocate W ★ θ)))
        world-extension-refl
        (SemanticProof.store-shift
          (seal-name (freshSealName W))
          W≤W₂ (store-typing runtime))


crossed-dynamic-runtime :
  ∀ {W W′ Φ Δᴸ Δᴿ ρ₀ ρ₁ ρ₂ θ θ′}
    {R : WorldRelation W W′} →
  (runtime : RuntimeNarrowing R Φ Δᴸ Δᴿ ρ₀ θ θ′) →
  NTI.LiftStoreⁱ
    ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ₀ ρ₁ →
  NTI.LiftStoreⁱ
    (swapRight∀∀ᵢ Φ) ρ₁ ρ₂ →
  RuntimeNarrowing
    (allocate-crossed
      {A₀ = ★} {A₁ = ★} {B₀ = ★} {B₁ = ★}
      {θA₀ = θ} {θA₁ = θ} {θB₀ = θ′} {θB₁ = θ′} R
      dynamic-type-narrowing
      (environments-narrow
        (type-environments-realized runtime))
      dynamic-type-narrowing
      (environments-narrow
        (type-environments-realized runtime)))
    (swapRight∀∀ᵢ Φ)
    (suc (suc Δᴸ)) (suc (suc Δᴿ))
    (NTI.crossedStoreⁱ wf★ wf★ wf★ wf★
      id★ id★ ρ₂)
    (seal-name (freshSealName (allocate W ★ θ)) ∷
      seal-name (freshSealName W) ∷ θ)
    (seal-name (freshSealName (allocate W′ ★ θ′)) ∷
      seal-name (freshSealName W′) ∷ θ′)
crossed-dynamic-runtime
    {W} {W′} {Φ} {Δᴸ} {Δᴿ}
    {ρ₀} {ρ₁} {ρ₂} {θ} {θ′} {R}
    runtime liftρ₁ liftρ₂ =
  runtime-narrowing
    (assumption-membership-unique-swap
      (assumption-membership-unique runtime))
    left-world
    right-world
    left-context
    right-context
    (runtime-type-seal
      (runtime-type-seal (right-runtime-environment runtime)))
    crossed-store-realization
    (crossed-type-environment-realization
      (type-environments-realized runtime))
    (s≤s (s≤s (abstract-supply runtime)))
  where
  types = type-environments-realized runtime
  θ~θ′ = environments-narrow types

  crossed =
    allocate-crossed
      {A₀ = ★} {A₁ = ★} {B₀ = ★} {B₁ = ★}
      {θA₀ = θ} {θA₁ = θ} {θB₀ = θ′} {θB₁ = θ′} R
      dynamic-type-narrowing θ~θ′
      dynamic-type-narrowing θ~θ′

  left-world :
    WorldTyping (allocate (allocate W ★ θ) ★ θ)
  left-world =
    allocate-world-typed
      (allocate-world-typed
        (left-world-typed runtime)
        (left-runtime-context runtime) wf★)
      (SemanticProof.runtime-context-weaken
        (world-extension-allocate world-extension-refl)
        (left-runtime-context runtime))
      wf★

  right-world :
    WorldTyping (allocate (allocate W′ ★ θ′) ★ θ′)
  right-world =
    allocate-world-typed
      (allocate-world-typed
        (right-world-typed runtime)
        (right-runtime-context runtime) wf★)
      (SemanticProof.runtime-context-weaken
        (world-extension-allocate world-extension-refl)
        (right-runtime-context runtime))
      wf★

  left-context :
    RuntimeContext
      (allocate (allocate W ★ θ) ★ θ)
      (suc (suc Δᴸ))
      (NTI.leftStoreⁱ
        (NTI.crossedStoreⁱ wf★ wf★ wf★ wf★
          id★ id★ ρ₂))
      (seal-name (freshSealName (allocate W ★ θ)) ∷
        seal-name (freshSealName W) ∷ θ)
  left-context
      rewrite sym (left-store-double-lift liftρ₁ liftρ₂) =
    crossed-runtime-context
      (left-world-typed runtime)
      (left-runtime-context runtime)

  right-context :
    RuntimeContext
      (allocate (allocate W′ ★ θ′) ★ θ′)
      (suc (suc Δᴿ))
      (NTI.rightStoreⁱ
        (NTI.crossedStoreⁱ wf★ wf★ wf★ wf★
          id★ id★ ρ₂))
      (seal-name (freshSealName (allocate W′ ★ θ′)) ∷
        seal-name (freshSealName W′) ∷ θ′)
  right-context
      rewrite sym (right-store-double-lift liftρ₁ liftρ₂) =
    crossed-runtime-context
      (right-world-typed runtime)
      (right-runtime-context runtime)

  weakened-store =
    store-correspondence-realization-weaken
      (extension-crossed extension-refl)
      (store-correspondences-realized runtime)

  lifted-store =
    paired-lift-store-correspondence-realization liftρ₂
      (paired-lift-store-correspondence-realization
        liftρ₁ weakened-store)

  crossed-store-realization :
    StoreCorrespondenceRealization crossed
      (swapRight∀∀ᵢ Φ)
      (suc (suc Δᴸ)) (suc (suc Δᴿ))
      (NTI.crossedStoreⁱ wf★ wf★ wf★ wf★
        id★ id★ ρ₂)
      (seal-name (freshSealName (allocate W ★ θ)) ∷
        seal-name (freshSealName W) ∷ θ)
      (seal-name (freshSealName (allocate W′ ★ θ′)) ∷
        seal-name (freshSealName W′) ∷ θ′)
  crossed-store-realization =
    store-correspondence-realization
      λ
        { (NTI.correspondence-stored
            (there (there (there (there (there
              (there member))))))) →
            realizes-store-correspondence lifted-store
              (NTI.correspondence-stored member)
        ; (NTI.correspondence-linked
            (there (there (there (there (here refl)))))) →
            freshSealName (allocate W ★ θ) ,
            freshSealName W′ ,
            refl , refl , link-cross-new-old
        ; (NTI.correspondence-linked
            (there (there (there (there (there
              (here refl))))))) →
            freshSealName W ,
            freshSealName (allocate W′ ★ θ′) ,
            refl , refl , link-cross-old-new
        ; (NTI.correspondence-linked
            (there (there (there (there (there
              (there member))))))) →
            realizes-store-correspondence lifted-store
              (NTI.correspondence-linked member)
        }
