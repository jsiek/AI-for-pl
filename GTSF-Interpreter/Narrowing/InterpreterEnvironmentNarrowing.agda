module Narrowing.InterpreterEnvironmentNarrowing where

-- File Charter:
--   * Exposes lookup and world-extension properties for captured term and
--     type environments.
--   * Connects successful interpreter lookup with related values or names.
--   * Delegates mutual value/environment weakening to a private proof module.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import proof.InterpreterValueNarrowingProof as Proof
open import Types using (TyVar)

module EnvironmentNarrowing
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Implementation = Proof.ValueNarrowingProof leaves

  data TypeIndexNarrowing :
      ∀ {W W′ θ θ′}
        {R : WorldRelation W W′} →
      (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
      TyVar → TyVar → Set₁ where
    here-both :
      ∀ {W W′ X X′ θ θ′}
        {R : WorldRelation W W′}
        {X~X′ : TypeNameNarrowing R X X′}
        {θ~θ′ : TypeEnvironmentNarrowing R θ θ′} →
      TypeIndexNarrowing
        (X~X′ ∷⊑∷ᵗᵉ θ~θ′) zero zero

    under-both :
      ∀ {W W′ X X′ θ θ′ x x′}
        {R : WorldRelation W W′}
        {X~X′ : TypeNameNarrowing R X X′}
        {θ~θ′ : TypeEnvironmentNarrowing R θ θ′} →
      TypeIndexNarrowing θ~θ′ x x′ →
      TypeIndexNarrowing
        (X~X′ ∷⊑∷ᵗᵉ θ~θ′) (suc x) (suc x′)

    under-left :
      ∀ {W W′ X θ θ′ x x′}
        {R : WorldRelation W W′}
        {X-ok : TypeNameScoped W X}
        {θ~θ′ : TypeEnvironmentNarrowing R θ θ′} →
      TypeIndexNarrowing θ~θ′ x x′ →
      TypeIndexNarrowing
        (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) (suc x) x′

    under-right :
      ∀ {W W′ X′ θ θ′ x x′}
        {R : WorldRelation W W′}
        {X′-ok : TypeNameScoped W′ X′}
        {θ~θ′ : TypeEnvironmentNarrowing R θ θ′} →
      TypeIndexNarrowing θ~θ′ x x′ →
      TypeIndexNarrowing
        (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) x (suc x′)

  type-environment-lookup-narrowing :
    ∀ {W W′ θ θ′ x x′}
      {R : WorldRelation W W′} →
    (θ~θ′ : TypeEnvironmentNarrowing R θ θ′) →
    TypeIndexNarrowing θ~θ′ x x′ →
    Σ[ X ∈ TypeName ]
    Σ[ X′ ∈ TypeName ]
      lookup θ x ≡ just X ×
      lookup θ′ x′ ≡ just X′ ×
      TypeNameNarrowing R X X′
  type-environment-lookup-narrowing
      (X~X′ ∷⊑∷ᵗᵉ θ~θ′) here-both =
    _ , _ , refl , refl , X~X′
  type-environment-lookup-narrowing
      (X~X′ ∷⊑∷ᵗᵉ θ~θ′) (under-both x~x′) =
    type-environment-lookup-narrowing θ~θ′ x~x′
  type-environment-lookup-narrowing
      (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) (under-left x~x′) =
    type-environment-lookup-narrowing θ~θ′ x~x′
  type-environment-lookup-narrowing
      (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) (under-right x~x′) =
    type-environment-lookup-narrowing θ~θ′ x~x′

  environment-lookup-narrowing :
    ∀ {W W′ γ γ′ x V}
      {R : WorldRelation W W′} →
    EnvironmentNarrowing R γ γ′ →
    lookup γ x ≡ just V →
    Σ[ V′ ∈ Value ]
      lookup γ′ x ≡ just V′ ×
      ValueNarrowing R V V′
  environment-lookup-narrowing []⊑[]ᵉ ()
  environment-lookup-narrowing {x = zero}
      (V~V′ ∷⊑∷ᵉ γ~γ′) refl =
    _ , refl , V~V′
  environment-lookup-narrowing {x = suc x}
      (V~V′ ∷⊑∷ᵉ γ~γ′) V-at =
    environment-lookup-narrowing γ~γ′ V-at

  value-narrowing-weaken :
    ∀ {W W′ U U′ V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    ValueNarrowing R V V′ →
    ValueNarrowing S V V′
  value-narrowing-weaken =
    Implementation.value-narrowing-weaken

  environment-narrowing-weaken :
    ∀ {W W′ U U′ γ γ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    EnvironmentNarrowing R γ γ′ →
    EnvironmentNarrowing S γ γ′
  environment-narrowing-weaken =
    Implementation.environment-narrowing-weaken

  value-narrowing-scoped :
    ∀ {W W′ V V′}
      {R : WorldRelation W W′} →
    ValueNarrowing R V V′ →
    ValueScoped W V × ValueScoped W′ V′
  value-narrowing-scoped =
    Implementation.value-narrowing-scoped

  environment-narrowing-scoped :
    ∀ {W W′ γ γ′}
      {R : WorldRelation W W′} →
    EnvironmentNarrowing R γ γ′ →
    EnvironmentScoped W γ × EnvironmentScoped W′ γ′
  environment-narrowing-scoped =
    Implementation.environment-narrowing-scoped
