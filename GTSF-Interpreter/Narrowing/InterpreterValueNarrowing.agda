module Narrowing.InterpreterValueNarrowing where

-- File Charter:
--   * Defines world-indexed narrowing for all eight semantic value forms.
--   * Relates closure bodies and both captured environments explicitly.
--   * Relates paired type abstractions extensionally after fresh nominal
--     instantiation, so their concrete binder names may differ.
--   * Relates source-only type abstractions extensionally after arbitrary
--     future left allocation and abstract-name replacement.
--   * Admits proof-only whole quotient cast frames only with world weakening
--     and sealed-head correspondence laws.
--   * Restricts asymmetric rules to named tag, proxy, and generalization
--     boundaries; there is no arbitrary value-wrapper relation.
--   * Leaves term and coercion evidence abstract for Milestone 3.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Coercions using (Coercion)
open import Interpreter
open import Narrowing.InterpreterWorldNarrowing
open import NuTerms using (Term)
open import Types

data NotSealed : Value → Set where
  closure-not-sealed :
    ∀ {N γ θ} →
    NotSealed (closure N γ θ)

  constant-not-sealed :
    ∀ {κ} →
    NotSealed (constant κ)

  tagged-not-sealed :
    ∀ {G} {gG : Ground G} {θ V} →
    NotSealed (tagged gG θ V)

  function-proxy-not-sealed :
    ∀ {p q θ V} →
    NotSealed (function-proxy p q θ V)

  type-abstraction-not-sealed :
    ∀ {X V} →
    NotSealed (type-abstraction X V)

  forall-proxy-not-sealed :
    ∀ {c θ V} →
    NotSealed (forall-proxy c θ V)

  generalized-not-sealed :
    ∀ {A c θ V} →
    NotSealed (generalized A c θ V)

data NameFresh : Name → Value → Set where
  fresh-closure :
    ∀ {X N γ θ} →
    abstract-name X ∉ θ →
    NameFresh X (closure N γ θ)

  fresh-constant :
    ∀ {X κ} →
    NameFresh X (constant κ)

  fresh-tagged :
    ∀ {X G} {gG : Ground G} {θ V} →
    abstract-name X ∉ θ →
    NameFresh X V →
    NameFresh X (tagged gG θ V)

  fresh-sealed :
    ∀ {X α V} →
    NameFresh X V →
    NameFresh X (sealed α V)

  fresh-function-proxy :
    ∀ {X p q θ V} →
    abstract-name X ∉ θ →
    NameFresh X V →
    NameFresh X (function-proxy p q θ V)

  fresh-type-abstraction-bound :
    ∀ {X V} →
    NameFresh X (type-abstraction X V)

  fresh-type-abstraction-free :
    ∀ {X Y V} →
    X ≢ Y →
    NameFresh X V →
    NameFresh X (type-abstraction Y V)

  fresh-forall-proxy :
    ∀ {X c θ V} →
    abstract-name X ∉ θ →
    NameFresh X V →
    NameFresh X (forall-proxy c θ V)

  fresh-generalized :
    ∀ {X A c θ V} →
    abstract-name X ∉ θ →
    NameFresh X V →
    NameFresh X (generalized A c θ V)

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
    TypeNarrowing : Ty → Ty → Set₁
    BodyNarrowing :
      ∀ {W W′} →
      (R : WorldNarrowing.WorldRelation TypeNarrowing W W′) →
      Environment → Environment →
      TypeEnvironment → TypeEnvironment →
      Term → Term → Set₁
    BodyNarrowingWeaken :
      ∀ {W W′ U U′ γ γ′ θ θ′ N N′}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      BodyNarrowing R γ γ′ θ θ′ N N′ →
      BodyNarrowing S γ γ′ θ θ′ N N′
    GroundNarrowing :
      ∀ {G H} → Ground G → Ground H → Set₁
    CoercionNarrowing :
      ∀ {W W′} →
      (R : WorldNarrowing.WorldRelation TypeNarrowing W W′) →
      TypeEnvironment → TypeEnvironment →
      Coercion → Coercion → Set₁
    CoercionNarrowingWeaken :
      ∀ {W W′ U U′ θ θ′ c c′}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      CoercionNarrowing R θ θ′ c c′ →
      CoercionNarrowing S θ θ′ c c′
    QuotientValueFrame :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      Value → Value → Value → Value → Set₁
    QuotientValueFrameWeaken :
      ∀ {W W′ U U′ V V′ L L′}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      QuotientValueFrame R V V′ L L′ →
      QuotientValueFrame S V V′ L L′
    QuotientValueFrameSealLink :
      ∀ {W W′ V V′ α α′ U U′}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′} →
      QuotientValueFrame R V V′
        (sealed α U) (sealed α′ U′) →
      WorldNarrowing.SealLink TypeNarrowing R α α′

    LeftTaggedBoundary :
      ∀ {G} → Ground G → Set₁
    RightTaggedBoundary :
      ∀ {G} → Ground G → Set₁

    LeftFunctionProxyBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Coercion → Coercion → Set₁
    LeftFunctionProxyBoundaryWeaken :
      ∀ {W W′ U U′ θ p q}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      LeftFunctionProxyBoundary R θ p q →
      LeftFunctionProxyBoundary S θ p q
    RightFunctionProxyBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Coercion → Coercion → Set₁
    RightFunctionProxyBoundaryWeaken :
      ∀ {W W′ U U′ θ′ p q}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      RightFunctionProxyBoundary R θ′ p q →
      RightFunctionProxyBoundary S θ′ p q

    LeftForallProxyBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Coercion → Set₁
    LeftForallProxyBoundaryWeaken :
      ∀ {W W′ U U′ θ c}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      LeftForallProxyBoundary R θ c →
      LeftForallProxyBoundary S θ c
    RightForallProxyBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Coercion → Set₁
    RightForallProxyBoundaryWeaken :
      ∀ {W W′ U U′ θ′ c}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      RightForallProxyBoundary R θ′ c →
      RightForallProxyBoundary S θ′ c

    LeftTypeAbstractionBoundary :
      Name → Set₁

    LeftGeneralizationBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Ty → Coercion → Set₁
    LeftGeneralizationBoundaryWeaken :
      ∀ {W W′ U U′ θ A c}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      LeftGeneralizationBoundary R θ A c →
      LeftGeneralizationBoundary S θ A c
    RightGeneralizationBoundary :
      ∀ {W W′} →
      WorldNarrowing.WorldRelation TypeNarrowing W W′ →
      TypeEnvironment → Ty → Coercion → Set₁
    RightGeneralizationBoundaryWeaken :
      ∀ {W W′ U U′ θ′ A c}
        {R : WorldNarrowing.WorldRelation TypeNarrowing W W′}
        {S : WorldNarrowing.WorldRelation TypeNarrowing U U′} →
      WorldNarrowing.WorldExtension TypeNarrowing R S →
      RightGeneralizationBoundary R θ′ A c →
      RightGeneralizationBoundary S θ′ A c

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
        BodyNarrowing leaves R γ γ′ θ θ′ N N′ →
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

      left-dynamic-sealed⊑ :
        ∀ {W W′ α V V′}
          {R : WorldRelation W W′} →
        LeftDynamicSeal R α →
        NotSealed V′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (sealed α V) V′

      function-proxy⊑ :
        ∀ {W W′ p p′ q q′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        CoercionNarrowing leaves R θ θ′ p p′ →
        CoercionNarrowing leaves R θ θ′ q q′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (function-proxy p q θ V)
          (function-proxy p′ q′ θ′ V′)

      type-abstraction⊑ :
        ∀ {W W′ X X′ V V′}
          {R : WorldRelation W W′} →
        TypeAbstractionNarrowing R X X′ V V′ →
        ValueNarrowing R
          (type-abstraction X V)
          (type-abstraction X′ V′)

      left-type-abstraction⊑ :
        ∀ {W W′ X V V′}
          {R : WorldRelation W W′} →
        LeftTypeAbstractionBoundary leaves X →
        LeftTypeAbstractionNarrowing R X V V′ →
        ValueNarrowing R (type-abstraction X V) V′

      forall-proxy⊑ :
        ∀ {W W′ c c′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        CoercionNarrowing leaves R θ θ′ c c′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (forall-proxy c θ V)
          (forall-proxy c′ θ′ V′)

      generalized⊑ :
        ∀ {W W′ A A′ c c′ θ θ′ V V′}
          {R : WorldRelation W W′} →
        TypeNarrowing leaves A A′ →
        CoercionNarrowing leaves R θ θ′ c c′ →
        TypeEnvironmentNarrowing R θ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R
          (generalized A c θ V)
          (generalized A′ c′ θ′ V′)

      quotient-value-frame⊑ :
        ∀ {W W′ V V′ U U′}
          {R : WorldRelation W W′} →
        QuotientValueFrame leaves R V V′ U U′ →
        ValueScoped W U →
        ValueScoped W′ U′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R U U′

      left-name-instantiated⊑ :
        ∀ {W W′ U U′ X α V V′ L}
          {R : WorldRelation W W′}
          {S : WorldRelation U U′} →
        WorldExtension R S →
        Allocated U α →
        substituteName X α V ≡ L →
        ValueNarrowing R V V′ →
        ValueNarrowing S L V′

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
        LeftFunctionProxyBoundary leaves R θ p q →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (function-proxy p q θ V) V′

      right-function-proxy⊑ :
        ∀ {W W′ p′ q′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightFunctionProxyBoundary leaves R θ′ p′ q′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (function-proxy p′ q′ θ′ V′)

      left-forall-proxy⊑ :
        ∀ {W W′ c θ V V′}
          {R : WorldRelation W W′} →
        LeftForallProxyBoundary leaves R θ c →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (forall-proxy c θ V) V′

      right-forall-proxy⊑ :
        ∀ {W W′ c′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightForallProxyBoundary leaves R θ′ c′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (forall-proxy c′ θ′ V′)

      left-generalized⊑ :
        ∀ {W W′ A c θ V V′}
          {R : WorldRelation W W′} →
        LeftGeneralizationBoundary leaves R θ A c →
        TypeEnvironmentScoped W θ →
        ValueNarrowing R V V′ →
        ValueNarrowing R (generalized A c θ V) V′

      right-generalized⊑ :
        ∀ {W W′ A′ c′ θ′ V V′}
          {R : WorldRelation W W′} →
        RightGeneralizationBoundary leaves R θ′ A′ c′ →
        TypeEnvironmentScoped W′ θ′ →
        ValueNarrowing R V V′ →
        ValueNarrowing R V (generalized A′ c′ θ′ V′)

    record TypeAbstractionNarrowing
        {W W′ : World}
        (R : WorldRelation W W′)
        (X X′ : Name)
        (V V′ : Value) : Set₁ where
      inductive
      constructor related-type-abstraction
      field
        left-body-scoped :
          ValueScoped W V
        right-body-scoped :
          ValueScoped W′ V′
        instantiate-bodies :
          ∀ {U U′ A A′ θ θ′}
            {S : WorldRelation U U′} →
          WorldExtension R S →
          (A~A′ : TypeNarrowing leaves A A′) →
          (θ~θ′ : TypeEnvironmentNarrowing S θ θ′) →
          ValueNarrowing
            (allocate-both S A~A′ θ~θ′)
            (substituteName X (freshSealName U) V)
            (substituteName X′ (freshSealName U′) V′)

    record LeftTypeAbstractionNarrowing
        {W W′ : World}
        (R : WorldRelation W W′)
        (X : Name)
        (V V′ : Value) : Set₁ where
      inductive
      constructor related-left-type-abstraction
      field
        left-source-body-scoped :
          ValueScoped W V
        right-target-scoped :
          ValueScoped W′ V′
        instantiate-left-body :
          ∀ {U U′ A σ}
            {S : WorldRelation U U′} →
          WorldExtension R S →
          (σ-ok : TypeEnvironmentScoped U σ) →
          ValueNarrowing
            (allocate-left-dynamic {A = A} S σ-ok)
            (substituteName X (freshSealName U) V)
            V′

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

  open TypeAbstractionNarrowing public
  open LeftTypeAbstractionNarrowing public
