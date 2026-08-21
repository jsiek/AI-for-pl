{-# OPTIONS --safe #-}

module proof.DGG.CenterRenamePlan where

-- File Charter:
--   * Defines structural center renaming over the two-context raw history.
--   * Inserts skipped centers and commutes kept centers through raw world
--     constructors without accepting a preassembled invariant record.
--   * Carries rebuilt freshness and type-imprecision premises explicitly,
--     preserves both endpoint Ctx indices, and proves the embedding and mark
--     renaming laws pointwise.
--   * Primary exports are CenterRenamePlan, renameCenter, and the center,
--     endpoint-embedding, mark, and direct-invariant preservation laws.
--     Dependencies are World and its direct invariants; there is no
--     bridge to the old World.

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
open import proof.DGG.World
open import proof.DGG.WorldInvariants


renameMarks : ∀ {Δ Δ′}
  → Δ ↪ᵗ Δ′
  → ImpEnv Δ
  → ImpEnv Δ′
renameMarks empty μ = λ Z → X⊑★
renameMarks (keep π) μ =
  extendᵐ (μ Fin.zero)
    (renameMarks π (λ X → μ (Fin.suc X)))
renameMarks (skip π) μ = extendᵐ X⊑★ (renameMarks π μ)


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

  renameMarks-id : ∀ {Δ} (μ : ImpEnv Δ) (Z : TyVar Δ)
    → renameMarks id↪ᵗ μ Z ≡ μ Z
  renameMarks-id {suc Δ} μ Fin.zero = refl
  renameMarks-id {suc Δ} μ (Fin.suc Z) =
    renameMarks-id (λ X → μ (Fin.suc X)) Z


mutual
  data CenterRenamePlan : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cᴿ)
      → ∀ {Δ′} → centerᶜ W ↪ᵗ Δ′ → Set where

    center-rename-id : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
        {π : centerᶜ W ↪ᵗ centerᶜ W}
      → π ≡ id↪ᵗ
      → CenterRenamePlan W π

    center-rename-insert : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
      → CenterRenamePlan W π
      → CenterRenamePlan W (skip π)

    center-rename-skip-center :
      ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
      → CenterRenamePlan W π
      → CenterRenamePlan (skip-centerᶜ W) (keep π)

    center-rename-lift-both :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′} {v : VarImp}
      → CenterRenamePlan W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlan
          (lift-both-rawᶜ W v Γᴸ⁺≡ Γᴿ⁺≡) (keep π)

    center-rename-lift-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
      → CenterRenamePlan W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → CenterRenamePlan
          (lift-left-rawᶜ W Γᴸ⁺≡) (keep π)

    center-rename-bind-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
      → CenterRenamePlan W π
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → CenterRenamePlan
          (bind-left-rawᶜ W A Γᴸ⁺≡) (keep π)

    center-rename-bind-right :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
        {fresh : RightBindFreshᶜ W B}
      → (plan : CenterRenamePlan W π)
      → (fresh′ : RightBindFreshᶜ (renameCenter plan) B)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlan
          (bind-right-rawᶜ W B fresh Γᴿ⁺≡) (keep π)

    center-rename-bind-both :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : CenterRenamePlan W π)
      → (represented′ : A ⊑ᵀ⟨ renameCenter plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlan
          (bind-both-rawᶜ W represented Γᴸ⁺≡ Γᴿ⁺≡) (keep π)

    center-rename-bind-both-star :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ⁺ : TermCtx (suc Δᴸ)} {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ⟨ W ⟩ B} {A≠★ : ⇑ᵗ A ≢ ★}
      → (plan : CenterRenamePlan W π)
      → (represented′ : A ⊑ᵀ⟨ renameCenter plan ⟩ B)
      → (Γᴸ⁺≡ : Γᴸ⁺ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ⁺≡ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → CenterRenamePlan
          (bind-both-star-rawᶜ W represented A≠★ Γᴸ⁺≡ Γᴿ⁺≡)
          (keep π)

    center-rename-bind-term :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : CenterRenamePlan W π)
      → (represented′ : A ⊑ᵀ⟨ renameCenter plan ⟩ B)
      → CenterRenamePlan (bind-termᶜ W represented) π

  renameCenter : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′}
      {π : centerᶜ W ↪ᵗ Δ′}
    → CenterRenamePlan W π
    → Cᴸ ⊑ᶜ Cᴿ
  renameCenter {W = W} (center-rename-id refl) = W
  renameCenter (center-rename-insert plan) =
    skip-centerᶜ (renameCenter plan)
  renameCenter (center-rename-skip-center plan) =
    skip-centerᶜ (renameCenter plan)
  renameCenter
      (center-rename-lift-both {v = v} plan Γᴸ⁺≡ Γᴿ⁺≡) =
    lift-both-rawᶜ (renameCenter plan) v Γᴸ⁺≡ Γᴿ⁺≡
  renameCenter (center-rename-lift-left plan Γᴸ⁺≡) =
    lift-left-rawᶜ (renameCenter plan) Γᴸ⁺≡
  renameCenter
      (center-rename-bind-left {A = A} plan Γᴸ⁺≡) =
    bind-left-rawᶜ (renameCenter plan) A Γᴸ⁺≡
  renameCenter
      (center-rename-bind-right {B = B} plan fresh′ Γᴿ⁺≡) =
    bind-right-rawᶜ (renameCenter plan) B fresh′ Γᴿ⁺≡
  renameCenter
      (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-rawᶜ (renameCenter plan) represented′ Γᴸ⁺≡ Γᴿ⁺≡
  renameCenter
      (center-rename-bind-both-star
        {A≠★ = A≠★} plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
    bind-both-star-rawᶜ (renameCenter plan) represented′ A≠★
      Γᴸ⁺≡ Γᴿ⁺≡
  renameCenter
      (center-rename-bind-term plan represented′) =
    bind-termᶜ (renameCenter plan) represented′


renameCenter-center : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′}
    {π : centerᶜ W ↪ᵗ Δ′}
    (plan : CenterRenamePlan W π)
  → centerᶜ (renameCenter plan) ≡ Δ′
renameCenter-center (center-rename-id refl) = refl
renameCenter-center (center-rename-insert plan) =
  cong suc (renameCenter-center plan)
renameCenter-center (center-rename-skip-center plan) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-lift-left plan Γᴸ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-bind-left plan Γᴸ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) =
  cong suc (renameCenter-center plan)
renameCenter-center
    (center-rename-bind-term plan represented′) =
  renameCenter-center plan


renameCenter-ηᴸ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′}
    {π : centerᶜ W ↪ᵗ Δ′}
    (plan : CenterRenamePlan W π)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (renameCenter plan)) X
    ≡ subst Fin.Fin (sym (renameCenter-center plan))
        (toRenameᵗ π (toRenameᵗ (ηᴸᶜ W) X))
renameCenter-ηᴸ (center-rename-id refl) X =
  sym (toRename-id-eq (toRenameᵗ _ X))
renameCenter-ηᴸ (center-rename-insert plan) X =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ (center-rename-skip-center plan) X =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴸ
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-lift-left plan Γᴸ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴸ
    (center-rename-lift-left plan Γᴸ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-bind-left plan Γᴸ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴸ
    (center-rename-bind-left plan Γᴸ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴸ
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴸ
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴸ
    (center-rename-bind-term plan represented′) X =
  renameCenter-ηᴸ plan X


renameCenter-ηᴿ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′}
    {π : centerᶜ W ↪ᵗ Δ′}
    (plan : CenterRenamePlan W π)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (renameCenter plan)) X
    ≡ subst Fin.Fin (sym (renameCenter-center plan))
        (toRenameᵗ π (toRenameᵗ (ηᴿᶜ W) X))
renameCenter-ηᴿ (center-rename-id refl) X =
  sym (toRename-id-eq (toRenameᵗ _ X))
renameCenter-ηᴿ (center-rename-insert plan) X =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ (center-rename-skip-center plan) X =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴿ
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-lift-left plan Γᴸ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-bind-left plan Γᴸ⁺≡) X =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴿ
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴿ
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero =
  sym (subst-Fin-zero-sym (renameCenter-center plan))
renameCenter-ηᴿ
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc X) =
  trans (cong Fin.suc (renameCenter-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (renameCenter-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
renameCenter-ηᴿ
    (center-rename-bind-term plan represented′) X =
  renameCenter-ηᴿ plan X


renameCenter-marks : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′}
    {π : centerᶜ W ↪ᵗ Δ′}
    (plan : CenterRenamePlan W π)
    (Z : TyVar (centerᶜ (renameCenter plan)))
  → marksᶜ (renameCenter plan) Z
    ≡ renameMarks π (marksᶜ W)
        (subst Fin.Fin (renameCenter-center plan) Z)
renameCenter-marks (center-rename-id refl) Z =
  sym (renameMarks-id _ Z)
renameCenter-marks
    (center-rename-insert plan) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-insert plan) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-skip-center plan) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-skip-center plan) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-lift-both plan Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-lift-left plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-lift-left plan Γᴸ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-bind-left plan Γᴸ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-bind-left plan Γᴸ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-bind-right plan fresh′ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-bind-both plan represented′ Γᴸ⁺≡ Γᴿ⁺≡)
    (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) Fin.zero
    rewrite subst-Fin-zero (renameCenter-center plan) = refl
renameCenter-marks
    (center-rename-bind-both-star
      plan represented′ Γᴸ⁺≡ Γᴿ⁺≡) (Fin.suc Z)
    rewrite subst-Fin-suc (renameCenter-center plan) Z =
  renameCenter-marks plan Z
renameCenter-marks
    (center-rename-bind-term plan represented′) Z =
  renameCenter-marks plan Z


renameCenter-direct-invariants : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Δ′} {π : centerᶜ W ↪ᵗ Δ′}
    (plan : CenterRenamePlan W π)
  → DirectWorldInvariantsᶜ (renameCenter plan)
renameCenter-direct-invariants plan =
  directInvariantsᶜ (renameCenter plan)
