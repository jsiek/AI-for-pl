{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxFreshBehindPlanProbe where

-- File Charter:
--   * Checks the structural source-fresh-behind operation needed by the live
--     strict-Lambda producer geometry.
--   * Commutes one source-only lift behind a constructor-form prefix of
--     target-star allocations.  Target aliases are deliberately not history
--     cases: they remain boundary-scoped TargetNameFocus/TargetAliasBoundary
--     evidence over the reconstructed stable world.
--   * Computes the output world, center permutation, old-center embedding,
--     endpoint laws, mark laws, and universal type-imprecision transport.
--     No post-world or invariant record is accepted by the plan.

open import Data.List using ([])
open import Data.Nat using (suc; zero)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyVar; ★; ＇_; renameᵗ; renameᵗ-cong; renameᵗ-comp)
open import TyStore using (TyStore; store-empty; store-bind; lookupStore)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using (X⊑★; _⊢_⊑_)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; ⇑ᵉᵗ)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-id-eq)
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldInvariants
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl


mutual
  data SourceFreshBehindPlanᶜ₀ : ∀ {Cᴸ Cʳ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cʳ)
      → Set where

    source-fresh-hereᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
      → SourceFreshBehindPlanᶜ₀ W

    source-fresh-behind-target-starᶜ₀ :
      ∀ {Δᴸ Δʳ} {Σᴸ : TyStore Δᴸ} {Σʳ : TyStore Δʳ}
        {Γᴸ : TermCtx Δᴸ} {Γʳ : TermCtx Δʳ}
        {Γʳ⁺ : TermCtx (suc Δʳ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δʳ , Σʳ , Γʳ ⟩}
      → SourceFreshBehindPlanᶜ₀ W
      → (Γʳ⁺≡ : Γʳ⁺ ≡ TC.⇑ᶜ Γʳ)
      → SourceFreshBehindPlanᶜ₀
          (bind-right-rawᶜ W ★ (inj₁ refl) Γʳ⁺≡)

  insertSourceFreshBehindᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    → SourceFreshBehindPlanᶜ₀ W
    → ⇑ᵉᵗ Cᴸ ⊑ᶜ Cʳ
  insertSourceFreshBehindᶜ₀ {W = W} source-fresh-hereᶜ₀ =
    lift-left-rawᶜ W refl
  insertSourceFreshBehindᶜ₀
      (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) =
    bind-right-rawᶜ (insertSourceFreshBehindᶜ₀ plan) ★
      (inj₁ refl) Γʳ⁺≡


oldCentersᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
  → (plan : SourceFreshBehindPlanᶜ₀ W)
  → centerᶜ W ↪ᵗ
      centerᶜ (insertSourceFreshBehindᶜ₀ plan)
oldCentersᶜ₀ source-fresh-hereᶜ₀ = skip id↪ᵗ
oldCentersᶜ₀ (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) =
  keep (oldCentersᶜ₀ plan)


freshCenterMapᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
  → (plan : SourceFreshBehindPlanᶜ₀ W)
  → TyVar (centerᶜ (liftLeftᶜ W))
  → TyVar (centerᶜ (insertSourceFreshBehindᶜ₀ plan))
freshCenterMapᶜ₀ source-fresh-hereᶜ₀ Z = Z
freshCenterMapᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    Fin.zero = Fin.suc (freshCenterMapᶜ₀ plan Fin.zero)
freshCenterMapᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc Fin.zero) = Fin.zero
freshCenterMapᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc (Fin.suc Z)) =
  Fin.suc (freshCenterMapᶜ₀ plan (Fin.suc Z))


freshCenterMap-injectiveᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W) {Y Z}
  → freshCenterMapᶜ₀ plan Y ≡ freshCenterMapᶜ₀ plan Z
  → Y ≡ Z
freshCenterMap-injectiveᶜ₀ source-fresh-hereᶜ₀ eq = eq
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.zero} {Fin.zero} eq = refl
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.zero} {Fin.suc Fin.zero} ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.zero} {Fin.suc (Fin.suc Z)} eq
    with freshCenterMap-injectiveᶜ₀ plan (fin-suc-injective eq)
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.zero} {Fin.suc (Fin.suc Z)} eq | ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc Fin.zero} {Fin.zero} ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc Fin.zero} {Fin.suc Fin.zero} eq = refl
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc Fin.zero} {Fin.suc (Fin.suc Z)} ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.zero} eq
    with freshCenterMap-injectiveᶜ₀ plan (fin-suc-injective eq)
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.zero} eq | ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.suc Fin.zero} ()
freshCenterMap-injectiveᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.suc (Fin.suc Z)} eq =
  cong Fin.suc
    (freshCenterMap-injectiveᶜ₀ plan (fin-suc-injective eq))


fresh-behind-sourceᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (X : TyVar (suc (Δᵉ Cᴸ)))
  → toRenameᵗ (ηᴸᶜ (insertSourceFreshBehindᶜ₀ plan)) X
    ≡ freshCenterMapᶜ₀ plan
        (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W)) X)
fresh-behind-sourceᶜ₀ source-fresh-hereᶜ₀ X = refl
fresh-behind-sourceᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) Fin.zero =
  cong Fin.suc (fresh-behind-sourceᶜ₀ plan Fin.zero)
fresh-behind-sourceᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc X) =
  cong Fin.suc (fresh-behind-sourceᶜ₀ plan (Fin.suc X))


fresh-behind-targetᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (X : TyVar (Δᵉ Cʳ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehindᶜ₀ plan)) X
    ≡ freshCenterMapᶜ₀ plan
        (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W)) X)
fresh-behind-targetᶜ₀ source-fresh-hereᶜ₀ X = refl
fresh-behind-targetᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) Fin.zero = refl
fresh-behind-targetᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc X) =
  cong Fin.suc (fresh-behind-targetᶜ₀ plan X)


fresh-behind-marksᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (Z : TyVar (centerᶜ (liftLeftᶜ W)))
  → marksᶜ (insertSourceFreshBehindᶜ₀ plan)
      (freshCenterMapᶜ₀ plan Z)
    ≡ marksᶜ (liftLeftᶜ W) Z
fresh-behind-marksᶜ₀ source-fresh-hereᶜ₀ Z = refl
fresh-behind-marksᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) Fin.zero =
  fresh-behind-marksᶜ₀ plan Fin.zero
fresh-behind-marksᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc Fin.zero) = refl
fresh-behind-marksᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc (Fin.suc Z)) =
  fresh-behind-marksᶜ₀ plan (Fin.suc Z)


fresh-map-old-centerᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (Z : TyVar (centerᶜ W))
  → freshCenterMapᶜ₀ plan (Fin.suc Z)
    ≡ toRenameᵗ (oldCentersᶜ₀ plan) Z
fresh-map-old-centerᶜ₀ source-fresh-hereᶜ₀ Z =
  cong Fin.suc (sym (toRename-id-eq Z))
fresh-map-old-centerᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) Fin.zero = refl
fresh-map-old-centerᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc Z) =
  cong Fin.suc (fresh-map-old-centerᶜ₀ plan Z)


fresh-behind-old-marksᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (insertSourceFreshBehindᶜ₀ plan)
      (toRenameᵗ (oldCentersᶜ₀ plan) Z)
    ≡ marksᶜ W Z
fresh-behind-old-marksᶜ₀ {W = W} plan Z =
  trans
    (cong (marksᶜ (insertSourceFreshBehindᶜ₀ plan))
      (sym (fresh-map-old-centerᶜ₀ plan Z)))
    (fresh-behind-marksᶜ₀ plan (Fin.suc Z))


fresh-behind-target-frozenᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (X : TyVar (Δᵉ Cʳ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehindᶜ₀ plan)) X
    ≡ toRenameᵗ (oldCentersᶜ₀ plan)
        (toRenameᵗ (ηᴿᶜ W) X)
fresh-behind-target-frozenᶜ₀ {W = W} plan X =
  trans (fresh-behind-targetᶜ₀ plan X)
    (fresh-map-old-centerᶜ₀ plan (toRenameᵗ (ηᴿᶜ W) X))


fresh-behind-old-source-frozenᶜ₀ :
    ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (insertSourceFreshBehindᶜ₀ plan))
      (Fin.suc X)
    ≡ toRenameᵗ (oldCentersᶜ₀ plan)
        (toRenameᵗ (ηᴸᶜ W) X)
fresh-behind-old-source-frozenᶜ₀ {W = W} plan X =
  trans (fresh-behind-sourceᶜ₀ plan (Fin.suc X))
    (fresh-map-old-centerᶜ₀ plan (toRenameᵗ (ηᴸᶜ W) X))


fresh-behind-transportᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    {A : Ty (suc (Δᵉ Cᴸ))} {B : Ty (Δᵉ Cʳ)}
    (plan : SourceFreshBehindPlanᶜ₀ W)
  → A ⊑ᵀ⟨ liftLeftᶜ W ⟩ B
  → A ⊑ᵀ⟨ insertSourceFreshBehindᶜ₀ plan ⟩ B
fresh-behind-transportᶜ₀ {W = W} {A = A} {B = B}
    plan represented =
  subst
    (λ L → marksᶜ (insertSourceFreshBehindᶜ₀ plan) ⊢ L ⊑
      renameᵗ (toRenameᵗ
        (ηᴿᶜ (insertSourceFreshBehindᶜ₀ plan))) B)
    (sym source-eq)
    (subst
      (λ R → marksᶜ (insertSourceFreshBehindᶜ₀ plan) ⊢
        renameᵗ (freshCenterMapᶜ₀ plan)
          (renameᵗ (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W))) A)
        ⊑ R)
      (sym target-eq)
      (rename-⊑ (freshCenterMapᶜ₀ plan)
        (freshCenterMap-injectiveᶜ₀ plan) star-map represented))
  where
  star-map : ∀ Z
    → marksᶜ (liftLeftᶜ W) Z ≡ X⊑★
    → marksᶜ (insertSourceFreshBehindᶜ₀ plan)
        (freshCenterMapᶜ₀ plan Z) ≡ X⊑★
  star-map Z mark = trans (fresh-behind-marksᶜ₀ plan Z) mark

  source-eq :
      renameᵗ (toRenameᵗ
        (ηᴸᶜ (insertSourceFreshBehindᶜ₀ plan))) A
    ≡ renameᵗ (freshCenterMapᶜ₀ plan)
        (renameᵗ (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W))) A)
  source-eq =
    trans (renameᵗ-cong A (fresh-behind-sourceᶜ₀ plan))
      (sym (renameᵗ-comp
        (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W)))
        (freshCenterMapᶜ₀ plan) A))

  target-eq :
      renameᵗ (toRenameᵗ
        (ηᴿᶜ (insertSourceFreshBehindᶜ₀ plan))) B
    ≡ renameᵗ (freshCenterMapᶜ₀ plan)
        (renameᵗ (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W))) B)
  target-eq =
    trans (renameᵗ-cong B (fresh-behind-targetᶜ₀ plan))
      (sym (renameᵗ-comp
        (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W)))
        (freshCenterMapᶜ₀ plan) B))


fresh-behind-invariantsᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
  → (plan : SourceFreshBehindPlanᶜ₀ W)
  → DirectWorldInvariantsᶜ (insertSourceFreshBehindᶜ₀ plan)
fresh-behind-invariantsᶜ₀ plan =
  directInvariantsᶜ (insertSourceFreshBehindᶜ₀ plan)


fresh-behind-not-targetᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
    (X : TyVar (Δᵉ Cʳ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehindᶜ₀ plan)) X
    ≢ toRenameᵗ (ηᴸᶜ (insertSourceFreshBehindᶜ₀ plan))
        Fin.zero
fresh-behind-not-targetᶜ₀ source-fresh-hereᶜ₀ X ()
fresh-behind-not-targetᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) Fin.zero ()
fresh-behind-not-targetᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡)
    (Fin.suc X) aligned =
  fresh-behind-not-targetᶜ₀ plan X (fin-suc-injective aligned)


fresh-behind-markᶜ₀ : ∀ {Cᴸ Cʳ} {W : Cᴸ ⊑ᶜ Cʳ}
    (plan : SourceFreshBehindPlanᶜ₀ W)
  → marksᶜ (insertSourceFreshBehindᶜ₀ plan)
      (toRenameᵗ (ηᴸᶜ (insertSourceFreshBehindᶜ₀ plan))
        Fin.zero)
    ≡ X⊑★
fresh-behind-markᶜ₀ source-fresh-hereᶜ₀ = refl
fresh-behind-markᶜ₀
    (source-fresh-behind-target-starᶜ₀ plan Γʳ⁺≡) =
  fresh-behind-markᶜ₀ plan


-- Exact producer geometry: alpha is allocated as a direct target star, then
-- the source binder is commuted behind alpha.  Beta := alpha is kept out of
-- the stable history and represented by the boundary-scoped alias focus.

empty-contextᶠ : Ctx
empty-contextᶠ = ⟨ zero , store-empty , [] ⟩

target-alpha-contextᶠ : Ctx
target-alpha-contextᶠ =
  ⟨ suc zero , store-bind store-empty ★ , [] ⟩

target-alpha-worldᶠ : empty-contextᶠ ⊑ᶜ target-alpha-contextᶠ
target-alpha-worldᶠ =
  bind-right-rawᶜ emptyᶜ ★ (inj₁ refl) refl

fresh-behind-alpha-planᶠ :
  SourceFreshBehindPlanᶜ₀ target-alpha-worldᶠ
fresh-behind-alpha-planᶠ =
  source-fresh-behind-target-starᶜ₀ source-fresh-hereᶜ₀ refl

stable-worldᶠ : ⇑ᵉᵗ empty-contextᶠ ⊑ᶜ target-alpha-contextᶠ
stable-worldᶠ = insertSourceFreshBehindᶜ₀ fresh-behind-alpha-planᶠ

stable-source-embeddingᶠ : ηᴸᶜ stable-worldᶠ ≡ skip (keep empty)
stable-source-embeddingᶠ = refl

stable-target-embeddingᶠ : ηᴿᶜ stable-worldᶠ ≡ keep (skip empty)
stable-target-embeddingᶠ = refl

stable-old-centersᶠ : oldCentersᶜ₀ fresh-behind-alpha-planᶠ
  ≡ keep (skip id↪ᵗ)
stable-old-centersᶠ = refl

source-Xᶠ : TyVar (Δᵉ (⇑ᵉᵗ empty-contextᶠ))
source-Xᶠ = Fin.zero

target-alphaᶠ : TyVar (Δᵉ target-alpha-contextᶠ)
target-alphaᶠ = Fin.zero

source-alpha-separatedᶠ :
  toRenameᵗ (ηᴸᶜ stable-worldᶠ) source-Xᶠ
    ≢ toRenameᵗ (ηᴿᶜ stable-worldᶠ) target-alphaᶠ
source-alpha-separatedᶠ ()

source-X-selfᶠ :
  lookupStore (Σᵉ (⇑ᵉᵗ empty-contextᶠ)) source-Xᶠ ≡ ＇ source-Xᶠ
source-X-selfᶠ = refl

source-alpha-representationsᶠ :
  lookupStore (Σᵉ (⇑ᵉᵗ empty-contextᶠ)) source-Xᶠ
    ⊑ᵀ⟨ stable-worldᶠ ⟩
  lookupStore (Σᵉ target-alpha-contextᶠ) target-alphaᶠ
source-alpha-representationsᶠ = Imprecision.X⊑★ refl

fresh-behind-alpha-focusᶠ :
  TargetNameFocusᶠ₀ stable-worldᶠ source-Xᶠ target-alphaᶠ
fresh-behind-alpha-focusᶠ =
  target-name-focusᶠ₀ source-alpha-separatedᶠ source-X-selfᶠ
    source-alpha-representationsᶠ

target-alpha-beta-contextᶠ : Ctx
target-alpha-beta-contextᶠ =
  ⟨ suc (suc zero) ,
    store-bind (store-bind store-empty ★) (＇ target-alphaᶠ) , [] ⟩

fresh-behind-alpha-boundaryᶠ :
  TargetAliasBoundaryᶠ₀ fresh-behind-alpha-focusᶠ
    target-alpha-beta-contextᶠ
fresh-behind-alpha-boundaryᶠ = target-alias-rawᶠ₀ refl

target-betaᶠ : TyVar (Δᵉ target-alpha-beta-contextᶠ)
target-betaᶠ = Fin.zero

target-alpha⁺ᶠ : TyVar (Δᵉ target-alpha-beta-contextᶠ)
target-alpha⁺ᶠ = Fin.suc target-alphaᶠ

target-beta-entryᶠ :
  lookupStore (Σᵉ target-alpha-beta-contextᶠ) target-betaᶠ
    ≡ ＇ target-alpha⁺ᶠ
target-beta-entryᶠ = refl

target-alpha-entryᶠ :
  lookupStore (Σᵉ target-alpha-beta-contextᶠ) target-alpha⁺ᶠ ≡ ★
target-alpha-entryᶠ = refl

fresh-behind-alias-surfaceᶠ :
  BoundaryTypeImprecisionᶠ₀ fresh-behind-alpha-boundaryᶠ
    (＇ source-Xᶠ) (＇ target-betaᶠ)
fresh-behind-alias-surfaceᶠ = Imprecision.X⊑X
