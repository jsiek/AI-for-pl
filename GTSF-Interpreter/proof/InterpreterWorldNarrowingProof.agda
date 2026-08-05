module proof.InterpreterWorldNarrowingProof where

-- File Charter:
--   * Proves structural properties of interpreter world narrowing.
--   * Establishes seal-link bounds, bijectivity, allocation lookup, and
--     weakening under world extension.
--   * Uses only the direct interpreter's data definitions.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (_<_; suc)
open import Data.Nat.Properties using
  (<-irrefl; <-trans; m<n⇒m<1+n; n<1+n)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (cong)

open import Interpreter
open import Narrowing.InterpreterWorldNarrowing
open import Types

module WorldNarrowingProof
  (TypeNarrowing : Ty → Ty → Set₁)
  where

  open WorldNarrowing TypeNarrowing

  seal-link-left-bound :
    ∀ {W W′ i α′} {R : WorldRelation W W′} →
    SealLink R (seal-name-id i) α′ →
    i < next-name W
  seal-link-left-bound link-here =
    n<1+n _
  seal-link-left-bound (link-under-both α~α′) =
    m<n⇒m<1+n (seal-link-left-bound α~α′)
  seal-link-left-bound (link-under-left α~α′) =
    m<n⇒m<1+n (seal-link-left-bound α~α′)
  seal-link-left-bound (link-under-right α~α′) =
    seal-link-left-bound α~α′
  seal-link-left-bound link-cross-old-new =
    m<n⇒m<1+n (n<1+n _)
  seal-link-left-bound link-cross-new-old =
    n<1+n _
  seal-link-left-bound (link-under-crossed α~α′) =
    m<n⇒m<1+n (m<n⇒m<1+n
      (seal-link-left-bound α~α′))

  seal-link-right-bound :
    ∀ {W W′ α i′} {R : WorldRelation W W′} →
    SealLink R α (seal-name-id i′) →
    i′ < next-name W′
  seal-link-right-bound link-here =
    n<1+n _
  seal-link-right-bound (link-under-both α~α′) =
    m<n⇒m<1+n (seal-link-right-bound α~α′)
  seal-link-right-bound (link-under-left α~α′) =
    seal-link-right-bound α~α′
  seal-link-right-bound (link-under-right α~α′) =
    m<n⇒m<1+n (seal-link-right-bound α~α′)
  seal-link-right-bound link-cross-old-new =
    n<1+n _
  seal-link-right-bound link-cross-new-old =
    m<n⇒m<1+n (n<1+n _)
  seal-link-right-bound (link-under-crossed α~α′) =
    m<n⇒m<1+n (m<n⇒m<1+n
      (seal-link-right-bound α~α′))

  left-dynamic-seal-bound :
    ∀ {W W′ i} {R : WorldRelation W W′} →
    LeftDynamicSeal R (seal-name-id i) →
    i < next-name W
  left-dynamic-seal-bound left-dynamic-here =
    n<1+n _
  left-dynamic-seal-bound
      (left-dynamic-under-both dynamic) =
    m<n⇒m<1+n (left-dynamic-seal-bound dynamic)
  left-dynamic-seal-bound
      (left-dynamic-under-left dynamic) =
    m<n⇒m<1+n (left-dynamic-seal-bound dynamic)
  left-dynamic-seal-bound
      (left-dynamic-under-right dynamic) =
    left-dynamic-seal-bound dynamic
  left-dynamic-seal-bound
      (left-dynamic-under-crossed dynamic) =
    m<n⇒m<1+n (m<n⇒m<1+n
      (left-dynamic-seal-bound dynamic))

  left-dynamic-seal-not-linked :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    LeftDynamicSeal R α →
    SealLink R α α′ →
    Data.Empty.⊥
  left-dynamic-seal-not-linked
      (left-dynamic-under-both dynamic)
      link-here =
    <-irrefl refl (left-dynamic-seal-bound dynamic)
  left-dynamic-seal-not-linked
      (left-dynamic-under-both dynamic)
      (link-under-both linked) =
    left-dynamic-seal-not-linked dynamic linked
  left-dynamic-seal-not-linked
      left-dynamic-here
      (link-under-left linked) =
    <-irrefl refl (seal-link-left-bound linked)
  left-dynamic-seal-not-linked
      (left-dynamic-under-left dynamic)
      (link-under-left linked) =
    left-dynamic-seal-not-linked dynamic linked
  left-dynamic-seal-not-linked
      (left-dynamic-under-right dynamic)
      (link-under-right linked) =
    left-dynamic-seal-not-linked dynamic linked
  left-dynamic-seal-not-linked
      (left-dynamic-under-crossed dynamic)
      link-cross-old-new =
    <-irrefl refl (left-dynamic-seal-bound dynamic)
  left-dynamic-seal-not-linked
      (left-dynamic-under-crossed dynamic)
      link-cross-new-old =
    <-irrefl refl
      (<-trans (left-dynamic-seal-bound dynamic) (n<1+n _))
  left-dynamic-seal-not-linked
      (left-dynamic-under-crossed dynamic)
      (link-under-crossed linked) =
    left-dynamic-seal-not-linked dynamic linked

  seal-link-functional :
    ∀ {W W′ α α′ β′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    SealLink R α β′ →
    α′ ≡ β′
  seal-link-functional link-here link-here =
    refl
  seal-link-functional link-here (link-under-both α~β′) =
    ⊥-elim (<-irrefl refl (seal-link-left-bound α~β′))
  seal-link-functional (link-under-both α~α′) link-here =
    ⊥-elim (<-irrefl refl (seal-link-left-bound α~α′))
  seal-link-functional
      (link-under-both α~α′)
      (link-under-both α~β′) =
    seal-link-functional α~α′ α~β′
  seal-link-functional
      (link-under-left α~α′)
      (link-under-left α~β′) =
    seal-link-functional α~α′ α~β′
  seal-link-functional
      (link-under-right α~α′)
      (link-under-right α~β′) =
    seal-link-functional α~α′ α~β′
  seal-link-functional link-cross-old-new link-cross-old-new =
    refl
  seal-link-functional link-cross-old-new
      (link-under-crossed α~β′) =
    ⊥-elim (<-irrefl refl (seal-link-left-bound α~β′))
  seal-link-functional link-cross-new-old link-cross-new-old =
    refl
  seal-link-functional link-cross-new-old
      (link-under-crossed α~β′) =
    ⊥-elim (<-irrefl refl
      (<-trans (seal-link-left-bound α~β′) (n<1+n _)))
  seal-link-functional (link-under-crossed α~α′)
      link-cross-old-new =
    ⊥-elim (<-irrefl refl (seal-link-left-bound α~α′))
  seal-link-functional (link-under-crossed α~α′)
      link-cross-new-old =
    ⊥-elim (<-irrefl refl
      (<-trans (seal-link-left-bound α~α′) (n<1+n _)))
  seal-link-functional (link-under-crossed α~α′)
      (link-under-crossed α~β′) =
    seal-link-functional α~α′ α~β′

  seal-link-injective :
    ∀ {W W′ α β α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    SealLink R β α′ →
    α ≡ β
  seal-link-injective link-here link-here =
    refl
  seal-link-injective link-here (link-under-both β~α′) =
    ⊥-elim (<-irrefl refl (seal-link-right-bound β~α′))
  seal-link-injective (link-under-both α~α′) link-here =
    ⊥-elim (<-irrefl refl (seal-link-right-bound α~α′))
  seal-link-injective
      (link-under-both α~α′)
      (link-under-both β~α′) =
    seal-link-injective α~α′ β~α′
  seal-link-injective
      (link-under-left α~α′)
      (link-under-left β~α′) =
    seal-link-injective α~α′ β~α′
  seal-link-injective
      (link-under-right α~α′)
      (link-under-right β~α′) =
    seal-link-injective α~α′ β~α′
  seal-link-injective link-cross-old-new link-cross-old-new =
    refl
  seal-link-injective link-cross-new-old link-cross-new-old =
    refl
  seal-link-injective link-cross-old-new
      (link-under-crossed β~α′) =
    ⊥-elim (<-irrefl refl
      (<-trans (seal-link-right-bound β~α′) (n<1+n _)))
  seal-link-injective link-cross-new-old
      (link-under-crossed β~α′) =
    ⊥-elim (<-irrefl refl (seal-link-right-bound β~α′))
  seal-link-injective (link-under-crossed α~α′)
      link-cross-old-new =
    ⊥-elim (<-irrefl refl
      (<-trans (seal-link-right-bound α~α′) (n<1+n _)))
  seal-link-injective (link-under-crossed α~α′)
      link-cross-new-old =
    ⊥-elim (<-irrefl refl (seal-link-right-bound α~α′))
  seal-link-injective (link-under-crossed α~α′)
      (link-under-crossed β~α′) =
    seal-link-injective α~α′ β~α′

  type-name-narrowing-functional :
    ∀ {W W′ X X′ Y′} {R : WorldRelation W W′} →
    TypeNameNarrowing R X X′ →
    TypeNameNarrowing R X Y′ →
    X′ ≡ Y′
  type-name-narrowing-functional abstract-name⊑ abstract-name⊑ =
    refl
  type-name-narrowing-functional
      (seal-name⊑ α~α′) (seal-name⊑ α~β′) =
    cong seal-name (seal-link-functional α~α′ α~β′)

  type-name-narrowing-injective :
    ∀ {W W′ X Y X′} {R : WorldRelation W W′} →
    TypeNameNarrowing R X X′ →
    TypeNameNarrowing R Y X′ →
    X ≡ Y
  type-name-narrowing-injective abstract-name⊑ abstract-name⊑ =
    refl
  type-name-narrowing-injective
      (seal-name⊑ α~α′) (seal-name⊑ β~α′) =
    cong seal-name (seal-link-injective α~α′ β~α′)

  seal-link-left-allocated :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Allocated W α
  seal-link-left-allocated link-here =
    allocated (here refl)
  seal-link-left-allocated (link-under-both α~α′)
      with seal-link-left-allocated α~α′
  seal-link-left-allocated (link-under-both α~α′)
      | allocated α∈W =
    allocated (there α∈W)
  seal-link-left-allocated (link-under-left α~α′)
      with seal-link-left-allocated α~α′
  seal-link-left-allocated (link-under-left α~α′)
      | allocated α∈W =
    allocated (there α∈W)
  seal-link-left-allocated (link-under-right α~α′) =
    seal-link-left-allocated α~α′
  seal-link-left-allocated link-cross-old-new =
    allocated (there (here refl))
  seal-link-left-allocated link-cross-new-old =
    allocated (here refl)
  seal-link-left-allocated (link-under-crossed α~α′)
      with seal-link-left-allocated α~α′
  seal-link-left-allocated (link-under-crossed α~α′)
      | allocated α∈W =
    allocated (there (there α∈W))

  seal-link-right-allocated :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Allocated W′ α′
  seal-link-right-allocated link-here =
    allocated (here refl)
  seal-link-right-allocated (link-under-both α~α′)
      with seal-link-right-allocated α~α′
  seal-link-right-allocated (link-under-both α~α′)
      | allocated α′∈W′ =
    allocated (there α′∈W′)
  seal-link-right-allocated (link-under-left α~α′) =
    seal-link-right-allocated α~α′
  seal-link-right-allocated (link-under-right α~α′)
      with seal-link-right-allocated α~α′
  seal-link-right-allocated (link-under-right α~α′)
      | allocated α′∈W′ =
    allocated (there α′∈W′)
  seal-link-right-allocated link-cross-old-new =
    allocated (here refl)
  seal-link-right-allocated link-cross-new-old =
    allocated (there (here refl))
  seal-link-right-allocated (link-under-crossed α~α′)
      with seal-link-right-allocated α~α′
  seal-link-right-allocated (link-under-crossed α~α′)
      | allocated α′∈W′ =
    allocated (there (there α′∈W′))

  world-extension-trans :
    ∀ {W W′ U U′ Z Z′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′}
      {T : WorldRelation Z Z′} →
    WorldExtension R S →
    WorldExtension S T →
    WorldExtension R T
  world-extension-trans R≤S extension-refl =
    R≤S
  world-extension-trans R≤S (extension-both S≤T) =
    extension-both (world-extension-trans R≤S S≤T)
  world-extension-trans R≤S (extension-left S≤T) =
    extension-left (world-extension-trans R≤S S≤T)
  world-extension-trans R≤S (extension-right S≤T) =
    extension-right (world-extension-trans R≤S S≤T)
  world-extension-trans R≤S (extension-crossed S≤T) =
    extension-crossed (world-extension-trans R≤S S≤T)

  seal-link-weaken :
    ∀ {W W′ U U′ α α′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    SealLink R α α′ →
    SealLink S α α′
  seal-link-weaken extension-refl α~α′ =
    α~α′
  seal-link-weaken (extension-both R≤S) α~α′ =
    link-under-both (seal-link-weaken R≤S α~α′)
  seal-link-weaken (extension-left R≤S) α~α′ =
    link-under-left (seal-link-weaken R≤S α~α′)
  seal-link-weaken (extension-right R≤S) α~α′ =
    link-under-right (seal-link-weaken R≤S α~α′)
  seal-link-weaken (extension-crossed R≤S) α~α′ =
    link-under-crossed (seal-link-weaken R≤S α~α′)

  type-name-narrowing-weaken :
    ∀ {W W′ U U′ X X′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeNameNarrowing R X X′ →
    TypeNameNarrowing S X X′
  type-name-narrowing-weaken R≤S abstract-name⊑ =
    abstract-name⊑
  type-name-narrowing-weaken R≤S (seal-name⊑ α~α′) =
    seal-name⊑ (seal-link-weaken R≤S α~α′)

  allocated-left-weaken :
    ∀ {W W′ U U′ α}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    Allocated W α →
    Allocated U α
  allocated-left-weaken extension-refl α∈W =
    α∈W
  allocated-left-weaken (extension-both R≤S) α∈W
      with allocated-left-weaken R≤S α∈W
  allocated-left-weaken (extension-both R≤S) α∈W
      | allocated α∈U =
    allocated (there α∈U)
  allocated-left-weaken (extension-left R≤S) α∈W
      with allocated-left-weaken R≤S α∈W
  allocated-left-weaken (extension-left R≤S) α∈W
      | allocated α∈U =
    allocated (there α∈U)
  allocated-left-weaken (extension-right R≤S) α∈W =
    allocated-left-weaken R≤S α∈W
  allocated-left-weaken (extension-crossed R≤S) α∈W
      with allocated-left-weaken R≤S α∈W
  allocated-left-weaken (extension-crossed R≤S) α∈W
      | allocated α∈U =
    allocated (there (there α∈U))

  allocated-right-weaken :
    ∀ {W W′ U U′ α′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    Allocated W′ α′ →
    Allocated U′ α′
  allocated-right-weaken extension-refl α′∈W′ =
    α′∈W′
  allocated-right-weaken (extension-both R≤S) α′∈W′
      with allocated-right-weaken R≤S α′∈W′
  allocated-right-weaken (extension-both R≤S) α′∈W′
      | allocated α′∈U′ =
    allocated (there α′∈U′)
  allocated-right-weaken (extension-left R≤S) α′∈W′ =
    allocated-right-weaken R≤S α′∈W′
  allocated-right-weaken (extension-right R≤S) α′∈W′
      with allocated-right-weaken R≤S α′∈W′
  allocated-right-weaken (extension-right R≤S) α′∈W′
      | allocated α′∈U′ =
    allocated (there α′∈U′)
  allocated-right-weaken (extension-crossed R≤S) α′∈W′
      with allocated-right-weaken R≤S α′∈W′
  allocated-right-weaken (extension-crossed R≤S) α′∈W′
      | allocated α′∈U′ =
    allocated (there (there α′∈U′))

  left-dynamic-seal-allocated :
    ∀ {W W′ α} {R : WorldRelation W W′} →
    LeftDynamicSeal R α →
    Allocated W α
  left-dynamic-seal-allocated left-dynamic-here =
    allocated (here refl)
  left-dynamic-seal-allocated
      (left-dynamic-under-both dynamic)
      with left-dynamic-seal-allocated dynamic
  left-dynamic-seal-allocated
      (left-dynamic-under-both dynamic)
      | allocated α∈W =
    allocated (there α∈W)
  left-dynamic-seal-allocated
      (left-dynamic-under-left dynamic)
      with left-dynamic-seal-allocated dynamic
  left-dynamic-seal-allocated
      (left-dynamic-under-left dynamic)
      | allocated α∈W =
    allocated (there α∈W)
  left-dynamic-seal-allocated
      (left-dynamic-under-right dynamic) =
    left-dynamic-seal-allocated dynamic
  left-dynamic-seal-allocated
      (left-dynamic-under-crossed dynamic)
      with left-dynamic-seal-allocated dynamic
  left-dynamic-seal-allocated
      (left-dynamic-under-crossed dynamic)
      | allocated α∈W =
    allocated (there (there α∈W))

  left-dynamic-seal-weaken :
    ∀ {W W′ U U′ α}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    LeftDynamicSeal R α →
    LeftDynamicSeal S α
  left-dynamic-seal-weaken extension-refl dynamic =
    dynamic
  left-dynamic-seal-weaken (extension-both R≤S) dynamic =
    left-dynamic-under-both
      (left-dynamic-seal-weaken R≤S dynamic)
  left-dynamic-seal-weaken (extension-left R≤S) dynamic =
    left-dynamic-under-left
      (left-dynamic-seal-weaken R≤S dynamic)
  left-dynamic-seal-weaken (extension-right R≤S) dynamic =
    left-dynamic-under-right
      (left-dynamic-seal-weaken R≤S dynamic)
  left-dynamic-seal-weaken (extension-crossed R≤S) dynamic =
    left-dynamic-under-crossed
      (left-dynamic-seal-weaken R≤S dynamic)

  type-name-left-scope-weaken :
    ∀ {W W′ U U′ X}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeNameScoped W X →
    TypeNameScoped U X
  type-name-left-scope-weaken R≤S abstract-scoped =
    abstract-scoped
  type-name-left-scope-weaken R≤S (seal-scoped α∈W) =
    seal-scoped (allocated-left-weaken R≤S α∈W)

  type-name-right-scope-weaken :
    ∀ {W W′ U U′ X′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeNameScoped W′ X′ →
    TypeNameScoped U′ X′
  type-name-right-scope-weaken R≤S abstract-scoped =
    abstract-scoped
  type-name-right-scope-weaken R≤S (seal-scoped α′∈W′) =
    seal-scoped (allocated-right-weaken R≤S α′∈W′)

  type-environment-narrowing-weaken :
    ∀ {W W′ U U′ θ θ′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeEnvironmentNarrowing R θ θ′ →
    TypeEnvironmentNarrowing S θ θ′
  type-environment-narrowing-weaken R≤S []⊑[]ᵗᵉ =
    []⊑[]ᵗᵉ
  type-environment-narrowing-weaken
      R≤S (X~X′ ∷⊑∷ᵗᵉ θ~θ′) =
    type-name-narrowing-weaken R≤S X~X′ ∷⊑∷ᵗᵉ
      type-environment-narrowing-weaken R≤S θ~θ′
  type-environment-narrowing-weaken
      R≤S (X-ok ∷ˡ⊑ᵗᵉ θ~θ′) =
    type-name-left-scope-weaken R≤S X-ok ∷ˡ⊑ᵗᵉ
      type-environment-narrowing-weaken R≤S θ~θ′
  type-environment-narrowing-weaken
      R≤S (X′-ok ∷ʳ⊑ᵗᵉ θ~θ′) =
    type-name-right-scope-weaken R≤S X′-ok ∷ʳ⊑ᵗᵉ
      type-environment-narrowing-weaken R≤S θ~θ′

  seal-link-respects-allocations :
    ∀ {W W′ α α′} {R : WorldRelation W W′} →
    SealLink R α α′ →
    Σ[ A ∈ Ty ]
    Σ[ θ ∈ TypeEnvironment ]
    Σ[ A′ ∈ Ty ]
    Σ[ θ′ ∈ TypeEnvironment ]
      allocation α A θ ∈ allocations W ×
      allocation α′ A′ θ′ ∈ allocations W′ ×
      TypeNarrowing A A′ ×
      TypeEnvironmentNarrowing R θ θ′
  seal-link-respects-allocations
      (link-here {A = A} {A′} {θ} {θ′}
        {A⊑A′ = A~A′} {θ⊑θ′ = θ~θ′}) =
    A , θ , A′ , θ′ ,
    here refl ,
    here refl ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-both extension-refl) θ~θ′
  seal-link-respects-allocations (link-under-both α~α′)
      with seal-link-respects-allocations α~α′
  seal-link-respects-allocations (link-under-both α~α′)
      | A , θ , A′ , θ′ , α∈W , α′∈W′ , A~A′ , θ~θ′ =
    A , θ , A′ , θ′ ,
    there α∈W ,
    there α′∈W′ ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-both extension-refl) θ~θ′
  seal-link-respects-allocations (link-under-left α~α′)
      with seal-link-respects-allocations α~α′
  seal-link-respects-allocations (link-under-left α~α′)
      | A , θ , A′ , θ′ , α∈W , α′∈W′ , A~A′ , θ~θ′ =
    A , θ , A′ , θ′ ,
    there α∈W ,
    α′∈W′ ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-left extension-refl) θ~θ′
  seal-link-respects-allocations (link-under-right α~α′)
      with seal-link-respects-allocations α~α′
  seal-link-respects-allocations (link-under-right α~α′)
      | A , θ , A′ , θ′ , α∈W , α′∈W′ , A~A′ , θ~θ′ =
    A , θ , A′ , θ′ ,
    α∈W ,
    there α′∈W′ ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-right extension-refl) θ~θ′
  seal-link-respects-allocations
      (link-cross-old-new
        {A₀ = A} {B₁ = A′} {θA₀ = θ} {θB₁ = θ′}
        {A₀⊑B₁ = A~A′} {θA₀⊑θB₁ = θ~θ′}) =
    A , θ , A′ , θ′ ,
    there (here refl) ,
    here refl ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-crossed extension-refl) θ~θ′
  seal-link-respects-allocations
      (link-cross-new-old
        {A₁ = A} {B₀ = A′} {θA₁ = θ} {θB₀ = θ′}
        {A₁⊑B₀ = A~A′} {θA₁⊑θB₀ = θ~θ′}) =
    A , θ , A′ , θ′ ,
    here refl ,
    there (here refl) ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-crossed extension-refl) θ~θ′
  seal-link-respects-allocations (link-under-crossed α~α′)
      with seal-link-respects-allocations α~α′
  seal-link-respects-allocations (link-under-crossed α~α′)
      | A , θ , A′ , θ′ , α∈W , α′∈W′ , A~A′ , θ~θ′ =
    A , θ , A′ , θ′ ,
    there (there α∈W) ,
    there (there α′∈W′) ,
    A~A′ ,
    type-environment-narrowing-weaken
      (extension-crossed extension-refl) θ~θ′
