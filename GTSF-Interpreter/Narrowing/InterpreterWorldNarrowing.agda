module Narrowing.InterpreterWorldNarrowing where

-- File Charter:
--   * Defines one proof-relevant relation for interpreter allocation worlds.
--   * Derives seal-name correspondence from paired allocation history.
--   * Retains the actual stored type of every one-sided allocation.
--   * Relates captured type environments through that same correspondence.
--   * Contains no operational or reduction semantics.

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

open import Interpreter
open import Types

data Allocated (W : World) (α : SealName) : Set where
  allocated :
    ∀ {A θ} →
    allocation α A θ ∈ allocations W →
    Allocated W α

data TypeNameScoped (W : World) : TypeName → Set where
  abstract-scoped :
    ∀ {X} →
    TypeNameScoped W (abstract-name X)

  seal-scoped :
    ∀ {α} →
    Allocated W α →
    TypeNameScoped W (seal-name α)

data TypeEnvironmentScoped (W : World) :
    TypeEnvironment → Set where
  []-scoped :
    TypeEnvironmentScoped W []

  _∷-scoped_ :
    ∀ {X θ} →
    TypeNameScoped W X →
    TypeEnvironmentScoped W θ →
    TypeEnvironmentScoped W (X ∷ θ)

module WorldNarrowing
  (TypeNarrowing : Ty → Ty → Set₁)
  where

  mutual

    data WorldRelation : World → World → Set₁ where
      empty-world⊑ :
        WorldRelation emptyWorld emptyWorld

      allocate-both :
        ∀ {W W′ A A′ θ θ′} →
        (R : WorldRelation W W′) →
        TypeNarrowing A A′ →
        TypeEnvironmentNarrowing R θ θ′ →
        WorldRelation (allocate W A θ) (allocate W′ A′ θ′)

      allocate-left-dynamic :
        ∀ {W W′ A θ} →
        (R : WorldRelation W W′) →
        TypeEnvironmentScoped W θ →
        WorldRelation (allocate W A θ) W′

      allocate-right-only :
        ∀ {W W′ A′ θ′} →
        (R : WorldRelation W W′) →
        TypeEnvironmentScoped W′ θ′ →
        WorldRelation W (allocate W′ A′ θ′)

      allocate-crossed :
        ∀ {W W′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁} →
        (R : WorldRelation W W′) →
        TypeNarrowing A₀ B₁ →
        TypeEnvironmentNarrowing R θA₀ θB₁ →
        TypeNarrowing A₁ B₀ →
        TypeEnvironmentNarrowing R θA₁ θB₀ →
        WorldRelation
          (allocate (allocate W A₀ θA₀) A₁ θA₁)
          (allocate (allocate W′ B₀ θB₀) B₁ θB₁)

    data SealLink :
        ∀ {W W′} →
        WorldRelation W W′ →
        SealName → SealName → Set₁ where
      link-here :
        ∀ {W W′ A A′ θ θ′}
          {R : WorldRelation W W′}
          {A⊑A′ : TypeNarrowing A A′}
          {θ⊑θ′ : TypeEnvironmentNarrowing R θ θ′} →
        SealLink
          (allocate-both R A⊑A′ θ⊑θ′)
          (freshSealName W)
          (freshSealName W′)

      link-under-both :
        ∀ {W W′ A A′ θ θ′ α α′}
          {R : WorldRelation W W′}
          {A⊑A′ : TypeNarrowing A A′}
          {θ⊑θ′ : TypeEnvironmentNarrowing R θ θ′} →
        SealLink R α α′ →
        SealLink (allocate-both R A⊑A′ θ⊑θ′) α α′

      link-under-left :
        ∀ {W W′ A θ α α′}
          {R : WorldRelation W W′}
          {θ-ok : TypeEnvironmentScoped W θ} →
        SealLink R α α′ →
        SealLink
          (allocate-left-dynamic {A = A} R θ-ok)
          α α′

      link-under-right :
        ∀ {W W′ A′ θ′ α α′}
          {R : WorldRelation W W′}
          {θ′-ok : TypeEnvironmentScoped W′ θ′} →
        SealLink R α α′ →
        SealLink (allocate-right-only {A′ = A′} R θ′-ok) α α′

      link-cross-old-new :
        ∀ {W W′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁}
          {R : WorldRelation W W′}
          {A₀⊑B₁ : TypeNarrowing A₀ B₁}
          {θA₀⊑θB₁ : TypeEnvironmentNarrowing R θA₀ θB₁}
          {A₁⊑B₀ : TypeNarrowing A₁ B₀}
          {θA₁⊑θB₀ : TypeEnvironmentNarrowing R θA₁ θB₀} →
        SealLink
          (allocate-crossed R A₀⊑B₁ θA₀⊑θB₁
            A₁⊑B₀ θA₁⊑θB₀)
          (freshSealName W)
          (freshSealName (allocate W′ B₀ θB₀))

      link-cross-new-old :
        ∀ {W W′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁}
          {R : WorldRelation W W′}
          {A₀⊑B₁ : TypeNarrowing A₀ B₁}
          {θA₀⊑θB₁ : TypeEnvironmentNarrowing R θA₀ θB₁}
          {A₁⊑B₀ : TypeNarrowing A₁ B₀}
          {θA₁⊑θB₀ : TypeEnvironmentNarrowing R θA₁ θB₀} →
        SealLink
          (allocate-crossed R A₀⊑B₁ θA₀⊑θB₁
            A₁⊑B₀ θA₁⊑θB₀)
          (freshSealName (allocate W A₀ θA₀))
          (freshSealName W′)

      link-under-crossed :
        ∀ {W W′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁ α α′}
          {R : WorldRelation W W′}
          {A₀⊑B₁ : TypeNarrowing A₀ B₁}
          {θA₀⊑θB₁ : TypeEnvironmentNarrowing R θA₀ θB₁}
          {A₁⊑B₀ : TypeNarrowing A₁ B₀}
          {θA₁⊑θB₀ : TypeEnvironmentNarrowing R θA₁ θB₀} →
        SealLink R α α′ →
        SealLink
          (allocate-crossed R A₀⊑B₁ θA₀⊑θB₁
            A₁⊑B₀ θA₁⊑θB₀)
          α α′

    data TypeNameNarrowing :
        ∀ {W W′} →
        WorldRelation W W′ →
        TypeName → TypeName → Set₁ where
      abstract-name⊑ :
        ∀ {W W′ X} {R : WorldRelation W W′} →
        TypeNameNarrowing R (abstract-name X) (abstract-name X)

      seal-name⊑ :
        ∀ {W W′ α α′} {R : WorldRelation W W′} →
        SealLink R α α′ →
        TypeNameNarrowing R (seal-name α) (seal-name α′)

    data TypeEnvironmentNarrowing :
        ∀ {W W′} →
        WorldRelation W W′ →
        TypeEnvironment → TypeEnvironment → Set₁ where
      []⊑[]ᵗᵉ :
        ∀ {W W′} {R : WorldRelation W W′} →
        TypeEnvironmentNarrowing R [] []

      _∷⊑∷ᵗᵉ_ :
        ∀ {W W′ X X′ θ θ′}
          {R : WorldRelation W W′} →
        TypeNameNarrowing R X X′ →
        TypeEnvironmentNarrowing R θ θ′ →
        TypeEnvironmentNarrowing
          R (X ∷ θ) (X′ ∷ θ′)

      _∷ˡ⊑ᵗᵉ_ :
        ∀ {W W′ X θ θ′}
          {R : WorldRelation W W′} →
        TypeNameScoped W X →
        TypeEnvironmentNarrowing R θ θ′ →
        TypeEnvironmentNarrowing R (X ∷ θ) θ′

      _∷ʳ⊑ᵗᵉ_ :
        ∀ {W W′ X′ θ θ′}
          {R : WorldRelation W W′} →
        TypeNameScoped W′ X′ →
        TypeEnvironmentNarrowing R θ θ′ →
        TypeEnvironmentNarrowing R θ (X′ ∷ θ′)

  data WorldExtension
      {W W′} (R : WorldRelation W W′) :
      ∀ {U U′} → WorldRelation U U′ → Set₁ where
    extension-refl :
      WorldExtension R R

    extension-both :
      ∀ {U U′ A A′ θ θ′}
        {S : WorldRelation U U′}
        {A⊑A′ : TypeNarrowing A A′}
        {θ⊑θ′ : TypeEnvironmentNarrowing S θ θ′} →
      WorldExtension R S →
      WorldExtension R (allocate-both S A⊑A′ θ⊑θ′)

    extension-left :
      ∀ {U U′ A θ}
        {S : WorldRelation U U′}
        {θ-ok : TypeEnvironmentScoped U θ} →
      WorldExtension R S →
      WorldExtension R
        (allocate-left-dynamic {A = A} S θ-ok)

    extension-right :
      ∀ {U U′ A′ θ′}
        {S : WorldRelation U U′}
        {θ′-ok : TypeEnvironmentScoped U′ θ′} →
      WorldExtension R S →
      WorldExtension
        R (allocate-right-only {A′ = A′} S θ′-ok)

    extension-crossed :
      ∀ {U U′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁}
        {S : WorldRelation U U′}
        {A₀⊑B₁ : TypeNarrowing A₀ B₁}
        {θA₀⊑θB₁ : TypeEnvironmentNarrowing S θA₀ θB₁}
        {A₁⊑B₀ : TypeNarrowing A₁ B₀}
        {θA₁⊑θB₀ : TypeEnvironmentNarrowing S θA₁ θB₀} →
      WorldExtension R S →
      WorldExtension R
        (allocate-crossed S A₀⊑B₁ θA₀⊑θB₁
          A₁⊑B₀ θA₁⊑θB₀)

  data LeftDynamicSeal :
      ∀ {W W′} →
      WorldRelation W W′ →
      SealName →
      Set₁ where
    left-dynamic-here :
      ∀ {W W′ A θ}
        {R : WorldRelation W W′}
        {θ-ok : TypeEnvironmentScoped W θ} →
      LeftDynamicSeal
        (allocate-left-dynamic {A = A} R θ-ok)
        (freshSealName W)

    left-dynamic-under-both :
      ∀ {W W′ A A′ θ θ′ α}
        {R : WorldRelation W W′}
        {A⊑A′ : TypeNarrowing A A′}
        {θ⊑θ′ : TypeEnvironmentNarrowing R θ θ′} →
      LeftDynamicSeal R α →
      LeftDynamicSeal
        (allocate-both R A⊑A′ θ⊑θ′) α

    left-dynamic-under-left :
      ∀ {W W′ A θ α}
        {R : WorldRelation W W′}
        {θ-ok : TypeEnvironmentScoped W θ} →
      LeftDynamicSeal R α →
      LeftDynamicSeal
        (allocate-left-dynamic {A = A} R θ-ok) α

    left-dynamic-under-right :
      ∀ {W W′ A′ θ′ α}
        {R : WorldRelation W W′}
        {θ′-ok : TypeEnvironmentScoped W′ θ′} →
      LeftDynamicSeal R α →
      LeftDynamicSeal
        (allocate-right-only {A′ = A′} R θ′-ok) α

    left-dynamic-under-crossed :
      ∀ {W W′ A₀ A₁ B₀ B₁ θA₀ θA₁ θB₀ θB₁ α}
        {R : WorldRelation W W′}
        {A₀⊑B₁ : TypeNarrowing A₀ B₁}
        {θA₀⊑θB₁ : TypeEnvironmentNarrowing R θA₀ θB₁}
        {A₁⊑B₀ : TypeNarrowing A₁ B₀}
        {θA₁⊑θB₀ : TypeEnvironmentNarrowing R θA₁ θB₀} →
      LeftDynamicSeal R α →
      LeftDynamicSeal
        (allocate-crossed R A₀⊑B₁ θA₀⊑θB₁
          A₁⊑B₀ θA₁⊑θB₀)
        α
