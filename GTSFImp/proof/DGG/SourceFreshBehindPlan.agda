{-# OPTIONS --safe #-}

module proof.DGG.SourceFreshBehindPlan where

-- File Charter:
--   * Defines the constructor-form plan that inserts one source-only lift
--     behind a prefix of direct target-star allocations.
--   * Interprets the plan as a raw two-context world and computes the center
--     map, old-center embedding, endpoint laws, mark laws, and type-
--     imprecision transport needed by source-only universal abstraction.
--   * Keeps target aliases outside the world history; they belong to the
--     exact boundary-focus layer built over the resulting stable world.
--   * Primary exports are SourceFreshBehindPlan, insertSourceFreshBehind,
--     and the sourceFreshBehind-* laws.  Dependencies are World and
--     its direct invariants, with no bridge to the old World.

open import Data.Nat using (suc)
open import Data.Sum using (inj₁)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyVar; ★; renameᵗ; renameᵗ-cong; renameᵗ-comp)
open import TyStore using (TyStore)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using (_↪ᵗ_; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using (X⊑★; _⊢_⊑_)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; ⇑ᵉᵗ)
open import proof.ImprecisionConsistency using (rename-⊑)
open import proof.TypeInTermSubst using (toRename-id-eq)
open import proof.DGG.World
open import proof.DGG.WorldInvariants


private
  fin-suc-injective : ∀ {n} {X Y : Fin.Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl


mutual
  data SourceFreshBehindPlan : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cᴿ)
      → Set where

    source-fresh-here : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
      → SourceFreshBehindPlan W

    source-fresh-behind-target-star :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      → SourceFreshBehindPlan W
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceFreshBehindPlan
          (bind-right-rawᶜ W ★ (inj₁ refl) Γᴿ⁺≡)

  insertSourceFreshBehind : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    → SourceFreshBehindPlan W
    → ⇑ᵉᵗ Cᴸ ⊑ᶜ Cᴿ
  insertSourceFreshBehind {W = W} source-fresh-here =
    lift-left-rawᶜ W refl
  insertSourceFreshBehind
      (source-fresh-behind-target-star plan Γᴿ⁺≡) =
    bind-right-rawᶜ (insertSourceFreshBehind plan) ★
      (inj₁ refl) Γᴿ⁺≡


sourceFreshBehind-oldCenters : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
  → (plan : SourceFreshBehindPlan W)
  → centerᶜ W ↪ᵗ centerᶜ (insertSourceFreshBehind plan)
sourceFreshBehind-oldCenters source-fresh-here = skip id↪ᵗ
sourceFreshBehind-oldCenters
    (source-fresh-behind-target-star plan Γᴿ⁺≡) =
  keep (sourceFreshBehind-oldCenters plan)


sourceFreshBehind-centerMap : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
  → (plan : SourceFreshBehindPlan W)
  → TyVar (centerᶜ (liftLeftᶜ W))
  → TyVar (centerᶜ (insertSourceFreshBehind plan))
sourceFreshBehind-centerMap source-fresh-here Z = Z
sourceFreshBehind-centerMap
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    Fin.zero = Fin.suc (sourceFreshBehind-centerMap plan Fin.zero)
sourceFreshBehind-centerMap
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc Fin.zero) = Fin.zero
sourceFreshBehind-centerMap
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc (Fin.suc Z)) =
  Fin.suc (sourceFreshBehind-centerMap plan (Fin.suc Z))


sourceFreshBehind-centerMap-injective :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W) {Y Z}
  → sourceFreshBehind-centerMap plan Y
      ≡ sourceFreshBehind-centerMap plan Z
  → Y ≡ Z
sourceFreshBehind-centerMap-injective source-fresh-here eq = eq
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.zero} {Fin.zero} eq = refl
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.zero} {Fin.suc Fin.zero} ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.zero} {Fin.suc (Fin.suc Z)} eq
    with sourceFreshBehind-centerMap-injective plan
      (fin-suc-injective eq)
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.zero} {Fin.suc (Fin.suc Z)} eq | ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc Fin.zero} {Fin.zero} ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc Fin.zero} {Fin.suc Fin.zero} eq = refl
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc Fin.zero} {Fin.suc (Fin.suc Z)} ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.zero} eq
    with sourceFreshBehind-centerMap-injective plan
      (fin-suc-injective eq)
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.zero} eq | ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.suc Fin.zero} ()
sourceFreshBehind-centerMap-injective
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    {Fin.suc (Fin.suc Y)} {Fin.suc (Fin.suc Z)} eq =
  cong Fin.suc
    (sourceFreshBehind-centerMap-injective plan
      (fin-suc-injective eq))


sourceFreshBehind-source : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (X : TyVar (suc (Δᵉ Cᴸ)))
  → toRenameᵗ (ηᴸᶜ (insertSourceFreshBehind plan)) X
    ≡ sourceFreshBehind-centerMap plan
        (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W)) X)
sourceFreshBehind-source source-fresh-here X = refl
sourceFreshBehind-source
    (source-fresh-behind-target-star plan Γᴿ⁺≡) Fin.zero =
  cong Fin.suc (sourceFreshBehind-source plan Fin.zero)
sourceFreshBehind-source
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc X) =
  cong Fin.suc (sourceFreshBehind-source plan (Fin.suc X))


sourceFreshBehind-target : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehind plan)) X
    ≡ sourceFreshBehind-centerMap plan
        (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W)) X)
sourceFreshBehind-target source-fresh-here X = refl
sourceFreshBehind-target
    (source-fresh-behind-target-star plan Γᴿ⁺≡) Fin.zero = refl
sourceFreshBehind-target
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc X) =
  cong Fin.suc (sourceFreshBehind-target plan X)


sourceFreshBehind-marks : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (Z : TyVar (centerᶜ (liftLeftᶜ W)))
  → marksᶜ (insertSourceFreshBehind plan)
      (sourceFreshBehind-centerMap plan Z)
    ≡ marksᶜ (liftLeftᶜ W) Z
sourceFreshBehind-marks source-fresh-here Z = refl
sourceFreshBehind-marks
    (source-fresh-behind-target-star plan Γᴿ⁺≡) Fin.zero =
  sourceFreshBehind-marks plan Fin.zero
sourceFreshBehind-marks
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc Fin.zero) = refl
sourceFreshBehind-marks
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc (Fin.suc Z)) =
  sourceFreshBehind-marks plan (Fin.suc Z)


sourceFreshBehind-old-center : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (Z : TyVar (centerᶜ W))
  → sourceFreshBehind-centerMap plan (Fin.suc Z)
    ≡ toRenameᵗ (sourceFreshBehind-oldCenters plan) Z
sourceFreshBehind-old-center source-fresh-here Z =
  cong Fin.suc (sym (toRename-id-eq Z))
sourceFreshBehind-old-center
    (source-fresh-behind-target-star plan Γᴿ⁺≡) Fin.zero = refl
sourceFreshBehind-old-center
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc Z) =
  cong Fin.suc (sourceFreshBehind-old-center plan Z)


sourceFreshBehind-old-marks : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (insertSourceFreshBehind plan)
      (toRenameᵗ (sourceFreshBehind-oldCenters plan) Z)
    ≡ marksᶜ W Z
sourceFreshBehind-old-marks {W = W} plan Z =
  trans
    (cong (marksᶜ (insertSourceFreshBehind plan))
      (sym (sourceFreshBehind-old-center plan Z)))
    (sourceFreshBehind-marks plan (Fin.suc Z))


sourceFreshBehind-target-frozen :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehind plan)) X
    ≡ toRenameᵗ (sourceFreshBehind-oldCenters plan)
        (toRenameᵗ (ηᴿᶜ W) X)
sourceFreshBehind-target-frozen {W = W} plan X =
  trans (sourceFreshBehind-target plan X)
    (sourceFreshBehind-old-center plan (toRenameᵗ (ηᴿᶜ W) X))


sourceFreshBehind-old-source-frozen :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (insertSourceFreshBehind plan)) (Fin.suc X)
    ≡ toRenameᵗ (sourceFreshBehind-oldCenters plan)
        (toRenameᵗ (ηᴸᶜ W) X)
sourceFreshBehind-old-source-frozen {W = W} plan X =
  trans (sourceFreshBehind-source plan (Fin.suc X))
    (sourceFreshBehind-old-center plan (toRenameᵗ (ηᴸᶜ W) X))


sourceFreshBehind-transport : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {A : Ty (suc (Δᵉ Cᴸ))} {B : Ty (Δᵉ Cᴿ)}
    (plan : SourceFreshBehindPlan W)
  → A ⊑ᵀ⟨ liftLeftᶜ W ⟩ B
  → A ⊑ᵀ⟨ insertSourceFreshBehind plan ⟩ B
sourceFreshBehind-transport {W = W} {A = A} {B = B}
    plan represented =
  subst
    (λ L → marksᶜ (insertSourceFreshBehind plan) ⊢ L ⊑
      renameᵗ (toRenameᵗ
        (ηᴿᶜ (insertSourceFreshBehind plan))) B)
    (sym source-eq)
    (subst
      (λ R → marksᶜ (insertSourceFreshBehind plan) ⊢
        renameᵗ (sourceFreshBehind-centerMap plan)
          (renameᵗ (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W))) A)
        ⊑ R)
      (sym target-eq)
      (rename-⊑ (sourceFreshBehind-centerMap plan)
        (sourceFreshBehind-centerMap-injective plan) star-map represented))
  where
  star-map : ∀ Z
    → marksᶜ (liftLeftᶜ W) Z ≡ X⊑★
    → marksᶜ (insertSourceFreshBehind plan)
        (sourceFreshBehind-centerMap plan Z) ≡ X⊑★
  star-map Z mark = trans (sourceFreshBehind-marks plan Z) mark

  source-eq :
      renameᵗ (toRenameᵗ
        (ηᴸᶜ (insertSourceFreshBehind plan))) A
    ≡ renameᵗ (sourceFreshBehind-centerMap plan)
        (renameᵗ (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W))) A)
  source-eq =
    trans (renameᵗ-cong A (sourceFreshBehind-source plan))
      (sym (renameᵗ-comp
        (toRenameᵗ (ηᴸᶜ (liftLeftᶜ W)))
        (sourceFreshBehind-centerMap plan) A))

  target-eq :
      renameᵗ (toRenameᵗ
        (ηᴿᶜ (insertSourceFreshBehind plan))) B
    ≡ renameᵗ (sourceFreshBehind-centerMap plan)
        (renameᵗ (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W))) B)
  target-eq =
    trans (renameᵗ-cong B (sourceFreshBehind-target plan))
      (sym (renameᵗ-comp
        (toRenameᵗ (ηᴿᶜ (liftLeftᶜ W)))
        (sourceFreshBehind-centerMap plan) B))


sourceFreshBehind-invariants : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
  → (plan : SourceFreshBehindPlan W)
  → DirectWorldInvariantsᶜ (insertSourceFreshBehind plan)
sourceFreshBehind-invariants plan =
  directInvariantsᶜ (insertSourceFreshBehind plan)


sourceFreshBehind-not-target : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (insertSourceFreshBehind plan)) X
    ≢ toRenameᵗ (ηᴸᶜ (insertSourceFreshBehind plan)) Fin.zero
sourceFreshBehind-not-target source-fresh-here X ()
sourceFreshBehind-not-target
    (source-fresh-behind-target-star plan Γᴿ⁺≡) Fin.zero ()
sourceFreshBehind-not-target
    (source-fresh-behind-target-star plan Γᴿ⁺≡)
    (Fin.suc X) aligned =
  sourceFreshBehind-not-target plan X (fin-suc-injective aligned)


sourceFreshBehind-mark : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    (plan : SourceFreshBehindPlan W)
  → marksᶜ (insertSourceFreshBehind plan)
      (toRenameᵗ (ηᴸᶜ (insertSourceFreshBehind plan)) Fin.zero)
    ≡ X⊑★
sourceFreshBehind-mark source-fresh-here = refl
sourceFreshBehind-mark
    (source-fresh-behind-target-star plan Γᴿ⁺≡) =
  sourceFreshBehind-mark plan
