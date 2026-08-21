{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxCenterRenamePlanProbe where

-- File Charter:
--   * Checks structural center renaming over the two-Ctx raw history.
--   * Inserts skipped centers and commutes kept centers through raw world
--     constructors without accepting a preassembled invariant record.
--   * Carries rebuilt freshness and type-imprecision premises explicitly,
--     preserves both endpoint Ctx indices, and proves the embedding and mark
--     renaming laws pointwise.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using (Ty; TyCtx; TyVar; ★; ⇑ᵗ)
open import TyStore using (TyStore)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; empty; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑★; extendᵐ)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ)
open import proof.TypeInTermSubst using (toRename-id-eq)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe


renameMarksᶜ₀ : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′
  → ImpEnv Δ
  → ImpEnv Δ′
renameMarksᶜ₀ empty μ = λ Z → X⊑★
renameMarksᶜ₀ (keep π) μ =
  extendᵐ (μ Fin.zero)
    (renameMarksᶜ₀ π (λ X → μ (Fin.suc X)))
renameMarksᶜ₀ (skip π) μ = extendᵐ X⊑★ (renameMarksᶜ₀ π μ)


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl

  subst-Fin-suc : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin m)
    → subst Fin.Fin (cong suc eq) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin eq X)
  subst-Fin-suc refl X = refl

  subst-Fin-zero : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (cong suc eq) Fin.zero ≡ Fin.zero
  subst-Fin-zero refl = refl

  renameMarks-idᶜ₀ : ∀ {Δ} (μ : ImpEnv Δ) (Z : TyVar Δ)
    → renameMarksᶜ₀ id↪ᵗ μ Z ≡ μ Z
  renameMarks-idᶜ₀ {suc Δ} μ Fin.zero = refl
  renameMarks-idᶜ₀ {suc Δ} μ (Fin.suc Z) =
    renameMarks-idᶜ₀ (λ X → μ (Fin.suc X)) Z


mutual
  data CenterRenamePlanᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
      → ∀ {Δ′} → centerᶜ₀ W ↪ᵗ Δ′ → Set where

    center-rename-idᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
        {π : centerᶜ₀ W ↪ᵗ centerᶜ₀ W}
      → π ≡ id↪ᵗ
      → CenterRenamePlanᶜ₀ W π

    center-rename-insertᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
      → CenterRenamePlanᶜ₀ W π
      → CenterRenamePlanᶜ₀ W (skip π)

    center-rename-skip-centerᶜ₀ :
      ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
      → CenterRenamePlanᶜ₀ W π
      → CenterRenamePlanᶜ₀ (skip-centerᶜ₀ W) (keep π)

    center-rename-lift-bothᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′} {v : VarImp}
      → CenterRenamePlanᶜ₀ W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlanᶜ₀
          (lift-both-rawᶜ₀ W v Γᴸ⁺≡ Γᴿ⁺≡) (keep π)

    center-rename-lift-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
      → CenterRenamePlanᶜ₀ W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → CenterRenamePlanᶜ₀
          (lift-left-rawᶜ₀ W Γᴸ⁺≡) (keep π)

    center-rename-bind-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
      → CenterRenamePlanᶜ₀ W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → CenterRenamePlanᶜ₀
          (bind-left-rawᶜ₀ W A Γᴸ⁺≡) (keep π)

    center-rename-bind-rightᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
        {fresh : RightBindFreshᶜ₀ W B}
      → (plan : CenterRenamePlanᶜ₀ W π)
      → (fresh′ : RightBindFreshᶜ₀ (renameCenterᶜ₀ plan) B)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlanᶜ₀
          (bind-right-rawᶜ₀ W B fresh Γᴿ⁺≡) (keep π)

    center-rename-bind-bothᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ₀⟨ W ⟩ B}
      → (plan : CenterRenamePlanᶜ₀ W π)
      → (represented′ : A ⊑ᵀ₀⟨ renameCenterᶜ₀ plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlanᶜ₀
          (bind-both-rawᶜ₀ W represented Γᴸ⁺≡ Γᴿ⁺≡) (keep π)

    center-rename-bind-both-starᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ₀⟨ W ⟩ B} {A≠★ : ⇑ᵗ A ≢ ★}
      → (plan : CenterRenamePlanᶜ₀ W π)
      → (represented′ : A ⊑ᵀ₀⟨ renameCenterᶜ₀ plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlanᶜ₀
          (bind-both-star-rawᶜ₀ W represented A≠★ Γᴸ⁺≡ Γᴿ⁺≡)
          (keep π)

    center-rename-bind-termᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ₀⟨ W ⟩ B}
      → (plan : CenterRenamePlanᶜ₀ W π)
      → (represented′ : A ⊑ᵀ₀⟨ renameCenterᶜ₀ plan ⟩ B)
      → CenterRenamePlanᶜ₀ (bind-termᶜ₀ W represented) π

  renameCenterᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′}
      {π : centerᶜ₀ W ↪ᵗ Δ′}
    → CenterRenamePlanᶜ₀ W π
    → Cᴸ ⊑ᶜ₀ Cᴿ
  renameCenterᶜ₀ {W = W} (center-rename-idᶜ₀ refl) = W
  renameCenterᶜ₀ (center-rename-insertᶜ₀ plan) =
    skip-centerᶜ₀ (renameCenterᶜ₀ plan)
  renameCenterᶜ₀ (center-rename-skip-centerᶜ₀ plan) =
    skip-centerᶜ₀ (renameCenterᶜ₀ plan)
  renameCenterᶜ₀
      (center-rename-lift-bothᶜ₀ {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡) =
    lift-both-rawᶜ₀ (renameCenterᶜ₀ plan) v Γᴸ⁺≡ Γᴿ⁺≡
  renameCenterᶜ₀ (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) =
    lift-left-rawᶜ₀ (renameCenterᶜ₀ plan) Γᴸ⁺≡
  renameCenterᶜ₀
      (center-rename-bind-leftᶜ₀ {A = A} plan Γᴸ⁺≡) =
    bind-left-rawᶜ₀ (renameCenterᶜ₀ plan) A Γᴸ⁺≡
  renameCenterᶜ₀
      (center-rename-bind-rightᶜ₀ {B = B} plan fresh′ Γᴿ⁺≡) =
    bind-right-rawᶜ₀ (renameCenterᶜ₀ plan) B fresh′ Γᴿ⁺≡
  renameCenterᶜ₀
      (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-rawᶜ₀ (renameCenterᶜ₀ plan) represented′ Γᴸ⁺≡ Γᴿ⁺≡
  renameCenterᶜ₀
      (center-rename-bind-both-starᶜ₀
        {A≠★ = A≠★} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-star-rawᶜ₀ (renameCenterᶜ₀ plan) represented′ A≠★
      Γᴸ⁺≡ Γᴿ⁺≡
  renameCenterᶜ₀
      (center-rename-bind-termᶜ₀ plan represented′) =
    bind-termᶜ₀ (renameCenterᶜ₀ plan) represented′


renameCenter-centerᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′}
    {π : centerᶜ₀ W ↪ᵗ Δ′}
    (plan : CenterRenamePlanᶜ₀ W π)
  → centerᶜ₀ (renameCenterᶜ₀ plan) ≡ Δ′
renameCenter-centerᶜ₀ (center-rename-idᶜ₀ refl) = refl
renameCenter-centerᶜ₀ (center-rename-insertᶜ₀ plan) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀ (center-rename-skip-centerᶜ₀ plan) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-centerᶜ₀ plan)
renameCenter-centerᶜ₀
    (center-rename-bind-termᶜ₀ plan represented′) =
  renameCenter-centerᶜ₀ plan


renameCenter-ηᴸᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′}
    {π : centerᶜ₀ W ↪ᵗ Δ′}
    (plan : CenterRenamePlanᶜ₀ W π)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ₀ (renameCenterᶜ₀ plan)) X
    ≡ subst Fin.Fin (sym (renameCenter-centerᶜ₀ plan))
        (toRenameᵗ π (toRenameᵗ (ηᴸᶜ₀ W) X))
renameCenter-ηᴸᶜ₀ (center-rename-idᶜ₀ refl) X =
  sym (toRename-id-eq (toRenameᵗ _ X))
renameCenter-ηᴸᶜ₀ (center-rename-insertᶜ₀ plan) X =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀ (center-rename-skip-centerᶜ₀ plan) X =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴸᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴸᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸᶜ₀
    (center-rename-bind-termᶜ₀ plan represented′) X =
  renameCenter-ηᴸᶜ₀ plan X


renameCenter-ηᴿᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′}
    {π : centerᶜ₀ W ↪ᵗ Δ′}
    (plan : CenterRenamePlanᶜ₀ W π)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ₀ (renameCenterᶜ₀ plan)) X
    ≡ subst Fin.Fin (sym (renameCenter-centerᶜ₀ plan))
        (toRenameᵗ π (toRenameᵗ (ηᴿᶜ₀ W) X))
renameCenter-ηᴿᶜ₀ (center-rename-idᶜ₀ refl) X =
  sym (toRename-id-eq (toRenameᵗ _ X))
renameCenter-ηᴿᶜ₀ (center-rename-insertᶜ₀ plan) X =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀ (center-rename-skip-centerᶜ₀ plan) X =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴿᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-centerᶜ₀ plan))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿᶜ₀
    (center-rename-bind-termᶜ₀ plan represented′) X =
  renameCenter-ηᴿᶜ₀ plan X


renameCenter-marksᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′}
    {π : centerᶜ₀ W ↪ᵗ Δ′}
    (plan : CenterRenamePlanᶜ₀ W π)
    (Z : TyVar (centerᶜ₀ (renameCenterᶜ₀ plan)))
  → marksᶜ₀ (renameCenterᶜ₀ plan) Z
    ≡ renameMarksᶜ₀ π (marksᶜ₀ W)
        (subst Fin.Fin (renameCenter-centerᶜ₀ plan) Z)
renameCenter-marksᶜ₀ (center-rename-idᶜ₀ refl) Z =
  sym (renameMarks-idᶜ₀ _ Z)
renameCenter-marksᶜ₀
    (center-rename-insertᶜ₀ plan) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-insertᶜ₀ plan) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-skip-centerᶜ₀ plan) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-skip-centerᶜ₀ plan) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-lift-bothᶜ₀ plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-lift-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-bind-leftᶜ₀ plan Γᴸ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-bind-rightᶜ₀ plan fresh′ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-bind-bothᶜ₀ plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-centerᶜ₀ plan) = refl
renameCenter-marksᶜ₀
    (center-rename-bind-both-starᶜ₀
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-centerᶜ₀ plan) Z =
  renameCenter-marksᶜ₀ plan Z
renameCenter-marksᶜ₀
    (center-rename-bind-termᶜ₀ plan represented′) Z =
  renameCenter-marksᶜ₀ plan Z


renameCenter-direct-invariantsᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Δ′} {π : centerᶜ₀ W ↪ᵗ Δ′}
    (plan : CenterRenamePlanᶜ₀ W π)
  → DirectWorldInvariantsᶜ₀ (renameCenterᶜ₀ plan)
renameCenter-direct-invariantsᶜ₀ plan =
  directInvariantsᶜ₀ (renameCenterᶜ₀ plan)
