module InterpreterValueNarrowing where

-- File Charter:
--   * Defines world-indexed narrowing for all eight semantic value forms.
--   * Relates closure bodies and both captured environments explicitly.
--   * Restricts asymmetric rules to named tag, proxy, and generalization
--     boundaries; there is no arbitrary value-wrapper relation.
--   * Leaves term and coercion evidence abstract for Milestone 3.

open import Data.List using ([]; _∷_)

open import Coercions using (Coercion)
open import Interpreter
open import InterpreterWorldNarrowing
open import NuTerms using (Term)
open import Types

mutual

  data ValueScoped : World → Value → Set where
    closure-scoped :
      ∀ {W N γ θ} →
      EnvironmentScoped W γ →
      TypeEnvironmentScoped W θ →
      ValueScoped W (closure N γ θ)

    constant-scoped :
      ∀ {W κ} →
      ValueScoped W (constant κ)

    tagged-scoped :
      ∀ {W G} {gG : Ground G} {θ V} →
      TypeEnvironmentScoped W θ →
      ValueScoped W V →
      ValueScoped W (tagged gG θ V)

    sealed-scoped :
      ∀ {W α V} →
      Allocated W α →
      ValueScoped W V →
      ValueScoped W (sealed α V)

    function-proxy-scoped :
      ∀ {W p q θ V} →
      TypeEnvironmentScoped W θ →
      ValueScoped W V →
      ValueScoped W (function-proxy p q θ V)

    type-abstraction-scoped :
      ∀ {W X V} →
      ValueScoped W V →
      ValueScoped W (type-abstraction X V)

    forall-proxy-scoped :
      ∀ {W c θ V} →
      TypeEnvironmentScoped W θ →
      ValueScoped W V →
      ValueScoped W (forall-proxy c θ V)

    generalized-scoped :
      ∀ {W A c θ V} →
      TypeEnvironmentScoped W θ →
      ValueScoped W V →
      ValueScoped W (generalized A c θ V)

  data EnvironmentScoped : World → Environment → Set where
    []-environment-scoped :
      ∀ {W} →
      EnvironmentScoped W []

    _∷-environment-scoped_ :
      ∀ {W V γ} →
      ValueScoped W V →
      EnvironmentScoped W γ →
      EnvironmentScoped W (V ∷ γ)

record NarrowingLeaves : Set₂ where
  field
    BodyNarrowing : Term → Term → Set₁
    TypeNarrowing : Ty → Ty → Set₁
    GroundNarrowing :
      ∀ {G H} → Ground G → Ground H → Set₁
    CoercionNarrowing : Coercion → Coercion → Set₁

    LeftTaggedBoundary :
      ∀ {G} → Ground G → Set₁
    RightTaggedBoundary :
      ∀ {G} → Ground G → Set₁

    LeftFunctionProxyBoundary :
      Coercion → Coercion → Set₁
    RightFunctionProxyBoundary :
      Coercion → Coercion → Set₁

    LeftForallProxyBoundary :
      Coercion → Set₁
    RightForallProxyBoundary :
      Coercion → Set₁

    LeftGeneralizationBoundary :
      Ty → Coercion → Set₁
    RightGeneralizationBoundary :
      Ty → Coercion → Set₁

open NarrowingLeaves public

module ValueNarrowing
  (leaves : NarrowingLeaves)
  where

  module RelatedWorlds = WorldNarrowing (TypeNarrowing leaves)
  open RelatedWorlds

  mutual

    data ValueNarrowing :
        ∀ {W W′} →
        WorldRelation W W′ →
        Value → Value → Set₁ where
      closure⊑ :
        ∀ {W W′ N N′ γ γ′ θ θ′}
          {R : WorldRelation W W′} →
        BodyNarrowing leaves N N′ →
        EnvironmentNarrowing R γ γ′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R
          (closure N γ θ)
          (closure N′ γ′ θ′)

      constant⊑ :
        ∀ {W W′} {R : WorldRelation W W′} κ →
        ValueNarrowing R (constant κ) (constant κ)

      tagged⊑ :
        ∀ {W W′ G H}
          {gG : Ground G} {gH : Ground H}
          {θ θ′ V V′} {R : WorldRelation W W′} →
        GroundNarrowing leaves gG gH →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (tagged gG θ V)
          (tagged gH θ′ V′)

      sealed⊑ :
        ∀ {W W′ α α′ V V′}
          {R : WorldRelation W W′} →
        SealLink R α α′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (sealed α V) (sealed α′ V′)

      function-proxy⊑ :
        ∀ {W W′ p p′ q q′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        CoercionNarrowing leaves p p′ →
        CoercionNarrowing leaves q q′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (function-proxy p q θ V)
          (function-proxy p′ q′ θ′ V′)

      type-abstraction⊑ :
        ∀ {W W′ X V V′}
          {R : WorldRelation W W′} →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (type-abstraction X V)
          (type-abstraction X V′)

      forall-proxy⊑ :
        ∀ {W W′ c c′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        CoercionNarrowing leaves c c′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (forall-proxy c θ V)
          (forall-proxy c′ θ′ V′)

      generalized⊑ :
        ∀ {W W′ A A′ c c′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        TypeNarrowing leaves A A′ →
        CoercionNarrowing leaves c c′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (generalized A c θ V)
          (generalized A′ c′ θ′ V′)

      left-tagged⊑ :
        ∀ {W W′ G} {gG : Ground G} {θ V V′}
          {R : WorldRelation W W′} →
        LeftTaggedBoundary leaves gG →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (tagged gG θ V) V′

      right-tagged⊑ :
        ∀ {W W′ H} {gH : Ground H} {θ′ V V′}
          {R : WorldRelation W W′} →
        RightTaggedBoundary leaves gH →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (tagged gH θ′ V′)

      left-function-proxy⊑ :
        ∀ {W W′ p q θ V V′}
          {R : WorldRelation W W′} →
        LeftFunctionProxyBoundary leaves p q →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (function-proxy p q θ V) V′

      right-function-proxy⊑ :
        ∀ {W W′ p′ q′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightFunctionProxyBoundary leaves p′ q′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (function-proxy p′ q′ θ′ V′)

      left-forall-proxy⊑ :
        ∀ {W W′ c θ V V′}
          {R : WorldRelation W W′} →
        LeftForallProxyBoundary leaves c →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (forall-proxy c θ V) V′

      right-forall-proxy⊑ :
        ∀ {W W′ c′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightForallProxyBoundary leaves c′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (forall-proxy c′ θ′ V′)

      left-generalized⊑ :
        ∀ {W W′ A c θ V V′}
          {R : WorldRelation W W′} →
        LeftGeneralizationBoundary leaves A c →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (generalized A c θ V) V′

      right-generalized⊑ :
        ∀ {W W′ A′ c′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightGeneralizationBoundary leaves A′ c′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (generalized A′ c′ θ′ V′)

    data EnvironmentNarrowing :
        ∀ {W W′} →
        WorldRelation W W′ →
        Environment → Environment → Set₁ where
      []⊑[]ᵉ :
        ∀ {W W′} {R : WorldRelation W W′} →
        EnvironmentNarrowing R [] []

      _∷⊑∷ᵉ_ :
        ∀ {W W′ V V′ γ γ′}
          {R : WorldRelation W W′} →
        ValueNarrowing R V V′ →
        EnvironmentNarrowing R γ γ′ →
        EnvironmentNarrowing R (V ∷ γ) (V′ ∷ γ′)
