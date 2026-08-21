{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxSourceRebasePlanProbe where

-- File Charter:
--   * Checks the smallest constructor-form source-rebase plan for the
--     two-Ctx world skeleton.
--   * Supports an already aligned identity and one source-only pivot moving
--     to a target-only allocation, then commutes either case through later
--     skipped centers and target-only allocations.
--   * Rebuilds only inductive worlds, so the four direct invariants follow
--     from the existing total invariant proof.  Target-only commutation keeps
--     separate freshness evidence for the rebuilt history.

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
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl


mutual
  data SourceRebasePlanᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
      → TyVar (Δᵉ Cᴸ)
      → TyVar (Δᵉ Cᴿ)
      → Set where

    source-rebase-idᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
      → toRenameᵗ (ηᴸᶜ₀ W) Xᴸ ≡ toRenameᵗ (ηᴿᶜ₀ W) Xᴿ
      → SourceRebasePlanᶜ₀ W Xᴸ Xᴿ

    source-to-targetᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → (fresh : RightBindFreshᶜ₀
          (bind-left-rawᶜ₀ W A Γᴸ⁺≡) B)
      → (represented : A ⊑ᵀ₀⟨ skip-centerᶜ₀ W ⟩ B)
      → (A≠★ : ⇑ᵗ A ≢ ★)
      → SourceRebasePlanᶜ₀
          (bind-right-rawᶜ₀
            (bind-left-rawᶜ₀ W A Γᴸ⁺≡)
            B fresh Γᴿ⁺≡)
          Fin.zero Fin.zero

    source-rebase-skipᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
      → SourceRebasePlanᶜ₀ W Xᴸ Xᴿ
      → SourceRebasePlanᶜ₀ (skip-centerᶜ₀ W) Xᴸ Xᴿ

    source-rebase-targetᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
        {fresh : RightBindFreshᶜ₀ W B}
      → (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
      → (fresh′ : RightBindFreshᶜ₀ (rebaseSourceᶜ₀ plan) B)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → SourceRebasePlanᶜ₀
          (bind-right-rawᶜ₀ W B fresh Γᴿ⁺≡)
          Xᴸ (Fin.suc Xᴿ)

  rebaseSourceᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    → SourceRebasePlanᶜ₀ W Xᴸ Xᴿ
    → Cᴸ ⊑ᶜ₀ Cᴿ
  rebaseSourceᶜ₀ {W = W} (source-rebase-idᶜ₀ aligned) = W
  rebaseSourceᶜ₀
      (source-to-targetᶜ₀ {W = W} Γᴸ⁺≡ Γᴿ⁺≡ fresh
        represented A≠★) =
    bind-both-star-rawᶜ₀ (skip-centerᶜ₀ W) represented A≠★
      Γᴸ⁺≡ Γᴿ⁺≡
  rebaseSourceᶜ₀ (source-rebase-skipᶜ₀ plan) =
    skip-centerᶜ₀ (rebaseSourceᶜ₀ plan)
  rebaseSourceᶜ₀
      (source-rebase-targetᶜ₀ {B = B} plan fresh′ Γᴿ⁺≡) =
    bind-right-rawᶜ₀ (rebaseSourceᶜ₀ plan) B fresh′ Γᴿ⁺≡


rebaseSource-centerᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
  → centerᶜ₀ (rebaseSourceᶜ₀ plan) ≡ centerᶜ₀ W
rebaseSource-centerᶜ₀ (source-rebase-idᶜ₀ aligned) = refl
rebaseSource-centerᶜ₀
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) =
  refl
rebaseSource-centerᶜ₀ (source-rebase-skipᶜ₀ plan) =
  cong suc (rebaseSource-centerᶜ₀ plan)
rebaseSource-centerᶜ₀
    (source-rebase-targetᶜ₀ plan fresh′ Γᴿ⁺≡) =
  cong suc (rebaseSource-centerᶜ₀ plan)


rebaseSource-ηᴸ-offᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ Yᴸ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
  → Yᴸ ≢ Xᴸ
  → toRenameᵗ (ηᴸᶜ₀ (rebaseSourceᶜ₀ plan)) Yᴸ
      ≡ subst Fin.Fin (sym (rebaseSource-centerᶜ₀ plan))
          (toRenameᵗ (ηᴸᶜ₀ W) Yᴸ)
rebaseSource-ηᴸ-offᶜ₀ (source-rebase-idᶜ₀ aligned) Y≠X = refl
rebaseSource-ηᴸ-offᶜ₀ {Yᴸ = Fin.zero}
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Y≠X =
  ⊥-elim (Y≠X refl)
rebaseSource-ηᴸ-offᶜ₀ {Yᴸ = Fin.suc Yᴸ}
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Y≠X =
  refl
rebaseSource-ηᴸ-offᶜ₀ (source-rebase-skipᶜ₀ {W = W} plan) Y≠X =
  trans (cong Fin.suc (rebaseSource-ηᴸ-offᶜ₀ plan Y≠X))
    (sym (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan)
      (toRenameᵗ (ηᴸᶜ₀ W) _)))
rebaseSource-ηᴸ-offᶜ₀
    (source-rebase-targetᶜ₀ {W = W} plan fresh′ Γᴿ⁺≡) Y≠X =
  trans (cong Fin.suc (rebaseSource-ηᴸ-offᶜ₀ plan Y≠X))
    (sym (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan)
      (toRenameᵗ (ηᴸᶜ₀ W) _)))


rebaseSource-ηᴿ-frozenᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
    (Yᴿ : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ₀ (rebaseSourceᶜ₀ plan)) Yᴿ
      ≡ subst Fin.Fin (sym (rebaseSource-centerᶜ₀ plan))
          (toRenameᵗ (ηᴿᶜ₀ W) Yᴿ)
rebaseSource-ηᴿ-frozenᶜ₀ (source-rebase-idᶜ₀ aligned) Yᴿ = refl
rebaseSource-ηᴿ-frozenᶜ₀
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    Fin.zero =
  refl
rebaseSource-ηᴿ-frozenᶜ₀
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★)
    (Fin.suc Yᴿ) =
  refl
rebaseSource-ηᴿ-frozenᶜ₀ (source-rebase-skipᶜ₀ {W = W} plan) Yᴿ =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozenᶜ₀ plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan)
      (toRenameᵗ (ηᴿᶜ₀ W) Yᴿ)))
rebaseSource-ηᴿ-frozenᶜ₀
    (source-rebase-targetᶜ₀ plan fresh′ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (rebaseSource-centerᶜ₀ plan))
rebaseSource-ηᴿ-frozenᶜ₀
    (source-rebase-targetᶜ₀ {W = W} plan fresh′ Γᴿ⁺≡)
    (Fin.suc Yᴿ) =
  trans (cong Fin.suc (rebaseSource-ηᴿ-frozenᶜ₀ plan Yᴿ))
    (sym (subst-Fin-suc-sym (rebaseSource-centerᶜ₀ plan)
      (toRenameᵗ (ηᴿᶜ₀ W) Yᴿ)))


rebaseSource-pivot-alignedᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
  → toRenameᵗ (ηᴸᶜ₀ (rebaseSourceᶜ₀ plan)) Xᴸ
      ≡ toRenameᵗ (ηᴿᶜ₀ (rebaseSourceᶜ₀ plan)) Xᴿ
rebaseSource-pivot-alignedᶜ₀ (source-rebase-idᶜ₀ aligned) = aligned
rebaseSource-pivot-alignedᶜ₀
    (source-to-targetᶜ₀ Γᴸ⁺≡ Γᴿ⁺≡ fresh represented A≠★) =
  refl
rebaseSource-pivot-alignedᶜ₀ (source-rebase-skipᶜ₀ plan) =
  cong Fin.suc (rebaseSource-pivot-alignedᶜ₀ plan)
rebaseSource-pivot-alignedᶜ₀
    (source-rebase-targetᶜ₀ plan fresh′ Γᴿ⁺≡) =
  cong Fin.suc (rebaseSource-pivot-alignedᶜ₀ plan)


rebaseSource-invariantsᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
  → DirectWorldInvariantsᶜ₀ (rebaseSourceᶜ₀ plan)
rebaseSource-invariantsᶜ₀ plan = directInvariantsᶜ₀ (rebaseSourceᶜ₀ plan)


sourceRebasePlan-soundᶜ₀ :
    ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Xᴸ Xᴿ}
    (plan : SourceRebasePlanᶜ₀ W Xᴸ Xᴿ)
  → RebaseSourceᶜ₀ W (rebaseSourceᶜ₀ plan) Xᴸ Xᴿ
sourceRebasePlan-soundᶜ₀ {Cᴸ = Cᴸ} {Cᴿ = Cᴿ}
    {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} plan =
  rebase-sourceᶜ₀
    (rebaseSource-centerᶜ₀ plan)
    (rebaseSource-ηᴸ-offᶜ₀ plan)
    (rebaseSource-ηᴿ-frozenᶜ₀ plan)
    aligned
    (representationsImpreciseᶜ₀ (rebaseSource-invariantsᶜ₀ plan) aligned)
  where
  aligned = rebaseSource-pivot-alignedᶜ₀ plan


-- These are the exact raw history heads intentionally absent from the
-- commutation plan.  Supporting them needs a separate local rewrite (and, for
-- term binding, transported term-entry imprecision), not another catch-all.
data UnsupportedSourceRebaseHeadᶜ₀ : Set where
  under-lift-bothᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
  under-lift-leftᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
  under-source-allocationᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
  under-paired-bindᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
  under-dynamic-paired-bindᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
  under-term-bindᶜ₀ : UnsupportedSourceRebaseHeadᶜ₀
