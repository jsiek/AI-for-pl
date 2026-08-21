{-# OPTIONS --safe #-}

module proof.DGG.SourceRebasePlan where

-- File Charter:
--   * Defines the constructor-form source-rebase plan for the two-context
--     world.
--   * Supports an already aligned identity and one source-only pivot moving
--     to a target-only allocation, then commutes either case through every
--     raw two-context history head.
--   * Rebuilds only inductive worlds, so the four direct invariants follow
--     from the total invariant proof.  Target-only commutation carries fresh
--     evidence for rebuilt history; term and paired bindings carry rebuilt
--     type imprecision explicitly.
--   * Primary exports are SourceRebasePlan, rebaseSource, and
--     sourceRebasePlan-sound; dependencies are World and its direct
--     invariants, with no compatibility world.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using (Ty; TyVar; ★; ⇑ᵗ)
open import TyStore using (TyStore)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using (toRenameᵗ)
open import Imprecision using (VarImp)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ)
open import proof.DGG.World
open import proof.DGG.WorldInvariants


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl


mutual
  data SourceRebasePlan : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cᴿ)
      → TyVar (Δᵉ Cᴸ)
      → TyVar (Δᵉ Cᴿ)
      → Set where

    source-rebase-id : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
      → toRenameᵗ (ηᴸᶜ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ W) Xᴿ
      → SourceRebasePlan W Xᴸ Xᴿ

    source-to-target :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → (fresh : RightBindFreshᶜ
          (bind-left-rawᶜ W A Γᴸ⁺≡) B)
      → (represented : A ⊑ᵀ⟨ skip-centerᶜ W ⟩ B)
      → (A≠★ : ⇑ᵗ A ≢ ★)
      → SourceRebasePlan
          (bind-right-rawᶜ
            (bind-left-rawᶜ W A Γᴸ⁺≡)
            B fresh Γᴿ⁺≡)
          Fin.zero Fin.zero

    source-rebase-skip : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
      → SourceRebasePlan W Xᴸ Xᴿ
      → SourceRebasePlan (skip-centerᶜ W) Xᴸ Xᴿ

    source-rebase-target :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {fresh : RightBindFreshᶜ W B}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (fresh′ : RightBindFreshᶜ (rebaseSource plan) B)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceRebasePlan
          (bind-right-rawᶜ W B fresh Γᴿ⁺≡)
          Xᴸ (Fin.suc Xᴿ)

    source-rebase-lift-both :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ} {v : VarImp}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceRebasePlan
          (lift-both-rawᶜ W v Γᴸ⁺≡ Γᴿ⁺≡)
          (Fin.suc Xᴸ) (Fin.suc Xᴿ)

    source-rebase-lift-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → SourceRebasePlan
          (lift-left-rawᶜ W Γᴸ⁺≡)
          (Fin.suc Xᴸ) Xᴿ

    source-rebase-bind-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → SourceRebasePlan
          (bind-left-rawᶜ W A Γᴸ⁺≡)
          (Fin.suc Xᴸ) Xᴿ

    source-rebase-bind-term :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (represented′ : A ⊑ᵀ⟨ rebaseSource plan ⟩ B)
      → SourceRebasePlan
          (bind-termᶜ W represented) Xᴸ Xᴿ

    source-rebase-bind-both :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (represented′ : A ⊑ᵀ⟨ rebaseSource plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceRebasePlan
          (bind-both-rawᶜ W represented Γᴸ⁺≡ Γᴿ⁺≡)
          (Fin.suc Xᴸ) (Fin.suc Xᴿ)

    source-rebase-bind-both-star :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {represented : A ⊑ᵀ⟨ W ⟩ B} {A≠★ : ⇑ᵗ A ≢ ★}
      → (plan : SourceRebasePlan W Xᴸ Xᴿ)
      → (represented′ : A ⊑ᵀ⟨ rebaseSource plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceRebasePlan
          (bind-both-star-rawᶜ W represented A≠★ Γᴸ⁺≡ Γᴿ⁺≡)
          (Fin.suc Xᴸ) (Fin.suc Xᴿ)

  rebaseSource : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    → SourceRebasePlan W Xᴸ Xᴿ
    → Cᴸ ⊑ᶜ Cᴿ
  rebaseSource {W = W} (source-rebase-id aligned) = W
  rebaseSource
      (source-to-target {W = W} Γᴸ⁺≡ Γᴿ⁺≡ fresh
        represented A≠★) =
    bind-both-star-rawᶜ (skip-centerᶜ W) represented A≠★
      Γᴸ⁺≡ Γᴿ⁺≡
  rebaseSource (source-rebase-skip plan) =
    skip-centerᶜ (rebaseSource plan)
  rebaseSource
      (source-rebase-target {B = B} plan fresh′ Γᴿ⁺≡) =
    bind-right-rawᶜ (rebaseSource plan) B fresh′ Γᴿ⁺≡
  rebaseSource
      (source-rebase-lift-both {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡) =
    lift-both-rawᶜ (rebaseSource plan) v Γᴸ⁺≡ Γᴿ⁺≡
  rebaseSource
      (source-rebase-lift-left plan Γᴸ⁺≡) =
    lift-left-rawᶜ (rebaseSource plan) Γᴸ⁺≡
  rebaseSource
      (source-rebase-bind-left {A = A} plan Γᴸ⁺≡) =
    bind-left-rawᶜ (rebaseSource plan) A Γᴸ⁺≡
  rebaseSource
      (source-rebase-bind-term plan represented′) =
    bind-termᶜ (rebaseSource plan) represented′
  rebaseSource
      (source-rebase-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-rawᶜ (rebaseSource plan) represented′ Γᴸ⁺≡ Γᴿ⁺≡
  rebaseSource
      (source-rebase-bind-both-star
        {A≠★ = A≠★} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-star-rawᶜ (rebaseSource plan) represented′ A≠★
      Γᴸ⁺≡ Γᴿ⁺≡


rebaseSource-center : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → centerᶜ (rebaseSource plan) ≡ centerᶜ W
rebaseSource-center (source-rebase-id aligned) = refl
rebaseSource-center
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) =
  refl
rebaseSource-center (source-rebase-skip plan) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-target plan fresh′ Γᴿ⁺≡) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-lift-left plan Γᴸ⁺≡) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-bind-left plan Γᴸ⁺≡) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-bind-term plan represented′) =
  rebaseSource-center plan
rebaseSource-center
    (source-rebase-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (rebaseSource-center plan)
rebaseSource-center
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (rebaseSource-center plan)


rebaseSource-ηᴸ-off :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ Yᴸ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → Yᴸ ≢ Xᴸ
  → toRenameᵗ (ηᴸᶜ (rebaseSource plan)) Yᴸ
      ≡ subst Fin.Fin (sym (rebaseSource-center plan))
          (toRenameᵗ (ηᴸᶜ W) Yᴸ)
rebaseSource-ηᴸ-off (source-rebase-id aligned) Y≠X = refl
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Y≠X =
  ⊥-elim (Y≠X refl)
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Y≠X =
  refl
rebaseSource-ηᴸ-off (source-rebase-skip {W = W} plan) Y≠X =
  trans (cong Fin.suc (rebaseSource-ηᴸ-off plan Y≠X))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) _)))
rebaseSource-ηᴸ-off
    (source-rebase-target {W = W} plan fresh′ Γᴿ⁺≡) Y≠X =
  trans (cong Fin.suc (rebaseSource-ηᴸ-off plan Y≠X))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) _)))
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-rebase-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-rebase-lift-both {W = W} plan Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  trans
    (cong Fin.suc
      (rebaseSource-ηᴸ-off plan
        (λ eq → Y≠X (cong Fin.suc eq))))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) Yᴸ)))
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-rebase-lift-left plan Γᴸ⁺≡) Y≠X =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-rebase-lift-left {W = W} plan Γᴸ⁺≡) Y≠X =
  trans
    (cong Fin.suc
      (rebaseSource-ηᴸ-off plan
        (λ eq → Y≠X (cong Fin.suc eq))))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) Yᴸ)))
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-rebase-bind-left plan Γᴸ⁺≡) Y≠X =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-rebase-bind-left {W = W} plan Γᴸ⁺≡) Y≠X =
  trans
    (cong Fin.suc
      (rebaseSource-ηᴸ-off plan
        (λ eq → Y≠X (cong Fin.suc eq))))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) Yᴸ)))
rebaseSource-ηᴸ-off
    (source-rebase-bind-term plan represented′) Y≠X =
  rebaseSource-ηᴸ-off plan Y≠X
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-rebase-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-rebase-bind-both
      {W = W} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  trans
    (cong Fin.suc
      (rebaseSource-ηᴸ-off plan
        (λ eq → Y≠X (cong Fin.suc eq))))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) Yᴸ)))
rebaseSource-ηᴸ-off {Yᴸ = Fin.zero}
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴸ-off {Yᴸ = Fin.suc Yᴸ}
    (source-rebase-bind-both-star
      {W = W} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Y≠X =
  trans
    (cong Fin.suc
      (rebaseSource-ηᴸ-off plan
        (λ eq → Y≠X (cong Fin.suc eq))))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴸᶜ W) Yᴸ)))


rebaseSource-ηᴿ-frozen :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
    (Yᴿ : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (rebaseSource plan)) Yᴿ
      ≡ subst Fin.Fin (sym (rebaseSource-center plan))
          (toRenameᵗ (ηᴿᶜ W) Yᴿ)
rebaseSource-ηᴿ-frozen (source-rebase-id aligned) Yᴿ = refl
rebaseSource-ηᴿ-frozen
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Fin.zero =
  refl
rebaseSource-ηᴿ-frozen
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    (Fin.suc Yᴿ) =
  refl
rebaseSource-ηᴿ-frozen (source-rebase-skip {W = W} plan) Yᴿ =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-target plan fresh′ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴿ-frozen
    (source-rebase-target {W = W} plan fresh′ Γᴿ⁺≡)
    (Fin.suc Yᴿ) =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴿ-frozen
    (source-rebase-lift-both {W = W} plan Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Yᴿ) =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-lift-left {W = W} plan Γᴸ⁺≡) Yᴿ =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-left {W = W} plan Γᴸ⁺≡) Yᴿ =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-term plan represented′) Yᴿ =
  rebaseSource-ηᴿ-frozen plan Yᴿ
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-both
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-both
      {W = W} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Yᴿ) =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (rebaseSource-center plan))
rebaseSource-ηᴿ-frozen
    (source-rebase-bind-both-star
      {W = W} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Yᴿ) =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozen plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-center plan)
      (toRenameᵗ (ηᴿᶜ W) Yᴿ)))


rebaseSource-pivot-aligned :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → toRenameᵗ (ηᴸᶜ (rebaseSource plan)) Xᴸ
      ≡ toRenameᵗ (ηᴿᶜ (rebaseSource plan)) Xᴿ
rebaseSource-pivot-aligned (source-rebase-id aligned) = aligned
rebaseSource-pivot-aligned
    (source-to-target Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) =
  refl
rebaseSource-pivot-aligned (source-rebase-skip plan) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-target plan fresh′ Γᴿ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-lift-left plan Γᴸ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-bind-left plan Γᴸ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-bind-term plan represented′) =
  rebaseSource-pivot-aligned plan
rebaseSource-pivot-aligned
    (source-rebase-bind-both
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)
rebaseSource-pivot-aligned
    (source-rebase-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-aligned plan)


rebaseSource-invariants :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → DirectWorldInvariantsᶜ (rebaseSource plan)
rebaseSource-invariants plan = directInvariantsᶜ (rebaseSource plan)


sourceRebasePlan-sound :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlan W Xᴸ Xᴿ)
  → RebaseSourceᶜ W (rebaseSource plan) Xᴸ Xᴿ
sourceRebasePlan-sound {Cᴸ = Cᴸ} {Cᴿ = Cᴿ}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} plan =
  rebase-sourceᶜ
    (rebaseSource-center plan)
    (rebaseSource-ηᴸ-off plan)
    (rebaseSource-ηᴿ-frozen plan)
    aligned
    (representationsImpreciseᶜ (rebaseSource-invariants plan) aligned)
  where
  aligned = rebaseSource-pivot-aligned plan
