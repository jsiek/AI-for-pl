module InterpreterEnvironmentNarrowing where

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
open import InterpreterValueNarrowing
open import InterpreterWorldNarrowing
import proof.InterpreterValueNarrowingProof as Proof

module EnvironmentNarrowing
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module Implementation = Proof.ValueNarrowingProof leaves

  type-environment-lookup-narrowing :
    ∀ {W W′ θ θ′ x X}
      {R : WorldRelation W W′} →
    TypeEnvironmentNarrowing R θ θ′ →
    lookup θ x ≡ just X →
    Σ[ X′ ∈ TypeName ]
      lookup θ′ x ≡ just X′ ×
      TypeNameNarrowing R X X′
  type-environment-lookup-narrowing []⊑[]ᵗᵉ ()
  type-environment-lookup-narrowing {x = zero}
      (X~X′ ∷⊑∷ᵗᵉ θ~θ′) refl =
    _ , refl , X~X′
  type-environment-lookup-narrowing {x = suc x}
      (X~X′ ∷⊑∷ᵗᵉ θ~θ′) X-at =
    type-environment-lookup-narrowing θ~θ′ X-at

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
