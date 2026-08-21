{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxTargetExtendPlanProbe where

-- File Charter:
--   * Checks structural target insertion over the two-Ctx raw world history.
--   * Starts with explicit fresh right-star or direct-alias insertion and
--     reconstructs skipped, lifted, source-bound, and target-bound heads.
--   * Computes the new world from the plan, derives its invariants from raw
--     history, and proves the center, embedding, mark, and direct-store laws.
--   * Stops before paired and term binding: those heads require a reusable
--     transport theorem for their relation-indexed type-imprecision premise.

open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-cong; renameᵗ-shift)
open import TyStore using
  (TyStore; lookupStore; store-lift; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using (ImpEnv; VarImp; X⊑★; extendᵐ)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
open import proof.TypeInTermSubst using
  (toRename-id-eq; toRename-wk-eq; toRename-keep-eq; renameᵗ-wk-eq)
open import proof.DGG.notes.probes.TwoCtxWorldSkeletonProbe
open import proof.DGG.notes.probes.TwoCtxWorldInvariantsProbe
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe


private
  subst-Fin-suc-sym : ∀ {m n} (eq : m ≡ n) (X : Fin.Fin n)
    → subst Fin.Fin (sym (cong suc eq)) (Fin.suc X)
      ≡ Fin.suc (subst Fin.Fin (sym eq) X)
  subst-Fin-suc-sym refl X = refl

  subst-Fin-zero-sym : ∀ {m n} (eq : m ≡ n)
    → subst Fin.Fin (sym (cong suc eq)) Fin.zero ≡ Fin.zero
  subst-Fin-zero-sym refl = refl

  renameᵗ-keep-shift : ∀ {Δ₀ Δ} (ρ : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
  renameᵗ-keep-shift ρ A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)


mutual
  data TargetExtendPlanᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ₀ Cᴿ)
      → (Cᴿ⁺ : Ctx)
      → (rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺)
      → ∀ {Δ⁺} → centerᶜ₀ W ↪ᵗ Δ⁺ → Set where

    target-extend-starᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ suc Δᴿ}
        {pi : centerᶜ₀ W ↪ᵗ suc (centerᶜ₀ W)}
      → (fresh : RightBindFreshᶜ₀ W ★)
      → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → rho ≡ skip id↪ᵗ
      → pi ≡ skip id↪ᵗ
      → TargetExtendPlanᶜ₀ W
          ⟨ suc Δᴿ , store-bind Σᴿ ★ , Γᴿ⁺ ⟩ rho pi

    target-extend-aliasᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {Y : TyVar Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ suc Δᴿ}
        {pi : centerᶜ₀ W ↪ᵗ suc (centerᶜ₀ W)}
      → (fresh : RightBindFreshᶜ₀ W (＇ Y))
      → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → rho ≡ skip id↪ᵗ
      → pi ≡ skip id↪ᵗ
      → TargetExtendPlanᶜ₀ W
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ Y) , Γᴿ⁺ ⟩ rho pi

    target-extend-skipᶜ₀ : ∀ {Cᴸ Cᴿ Cᴿ⁺}
        {W : Cᴸ ⊑ᶜ₀ Cᴿ} {rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → TargetExtendPlanᶜ₀ (skip-centerᶜ₀ W) Cᴿ⁺ rho (keep pi)

    target-extend-lift-bothᶜ₀ :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
        {v : VarImp}
      → TargetExtendPlanᶜ₀ W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (lift-both-rawᶜ₀ W v Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ , store-lift Σᴿ⁺ , Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-lift-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlanᶜ₀
          (lift-left-rawᶜ₀ W Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlanᶜ₀
          (bind-left-rawᶜ₀ W A Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-rightᶜ₀ :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ₀ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
        {fresh : RightBindFreshᶜ₀ W B}
      → (plan : TargetExtendPlanᶜ₀
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (fresh⁺ : RightBindFreshᶜ₀ (extendTargetᶜ₀ plan)
          (renameᵗ (toRenameᵗ rho) B))
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (bind-right-rawᶜ₀ W B fresh Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

  extendTargetᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
      {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
    → Cᴸ ⊑ᶜ₀ Cᴿ⁺
  extendTargetᶜ₀ {W = W}
      (target-extend-starᶜ₀ fresh eqᴿ refl refl) =
    bind-right-rawᶜ₀ W ★ fresh eqᴿ
  extendTargetᶜ₀ {W = W}
      (target-extend-aliasᶜ₀ {Y = Y} fresh eqᴿ refl refl) =
    bind-right-rawᶜ₀ W (＇ Y) fresh eqᴿ
  extendTargetᶜ₀ (target-extend-skipᶜ₀ plan) =
    skip-centerᶜ₀ (extendTargetᶜ₀ plan)
  extendTargetᶜ₀
      (target-extend-lift-bothᶜ₀ {v = v} plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    lift-both-rawᶜ₀ (extendTargetᶜ₀ plan) v Γᴸ≡ Γᴿ⁺≡
  extendTargetᶜ₀
      (target-extend-lift-leftᶜ₀ plan Γᴸ≡) =
    lift-left-rawᶜ₀ (extendTargetᶜ₀ plan) Γᴸ≡
  extendTargetᶜ₀
      (target-extend-bind-leftᶜ₀ {A = A} plan Γᴸ≡) =
    bind-left-rawᶜ₀ (extendTargetᶜ₀ plan) A Γᴸ≡
  extendTargetᶜ₀
      (target-extend-bind-rightᶜ₀ {B = B}
        plan fresh⁺ Γᴿ≡ Γᴿ⁺≡) =
    bind-right-rawᶜ₀ (extendTargetᶜ₀ plan)
      (renameᵗ (toRenameᵗ _) B) fresh⁺ Γᴿ⁺≡


extendTarget-centerᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
  → centerᶜ₀ (extendTargetᶜ₀ plan) ≡ Δ⁺
extendTarget-centerᶜ₀ (target-extend-starᶜ₀ fresh eqᴿ refl refl) = refl
extendTarget-centerᶜ₀ (target-extend-aliasᶜ₀ fresh eqᴿ refl refl) = refl
extendTarget-centerᶜ₀ (target-extend-skipᶜ₀ plan) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀ (target-extend-lift-bothᶜ₀ plan _ _ _) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀ (target-extend-lift-leftᶜ₀ plan _) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀ (target-extend-bind-leftᶜ₀ plan _) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀ (target-extend-bind-rightᶜ₀ plan _ _ _) =
  cong suc (extendTarget-centerᶜ₀ plan)


extendTarget-ηᴸᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ₀ (extendTargetᶜ₀ plan)) X
    ≡ subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴸᶜ₀ W) X))
extendTarget-ηᴸᶜ₀
    (target-extend-starᶜ₀ fresh eqᴿ refl refl) X =
  cong Fin.suc (sym (toRename-id-eq (toRenameᵗ _ X)))
extendTarget-ηᴸᶜ₀
    (target-extend-aliasᶜ₀ fresh eqᴿ refl refl) X =
  cong Fin.suc (sym (toRename-id-eq (toRenameᵗ _ X)))
extendTarget-ηᴸᶜ₀ (target-extend-skipᶜ₀ plan) X =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-lift-bothᶜ₀ plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴸᶜ₀
    (target-extend-lift-bothᶜ₀ plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴸᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) X =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))


extendTarget-ηᴿᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ₀ (extendTargetᶜ₀ plan))
      (toRenameᵗ rho X)
    ≡ subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴿᶜ₀ W) X))
extendTarget-ηᴿᶜ₀
    (target-extend-starᶜ₀ fresh eqᴿ refl refl) X =
  cong Fin.suc
    (trans (cong (toRenameᵗ _) (toRename-id-eq X))
      (sym (toRename-id-eq (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-aliasᶜ₀ fresh eqᴿ refl refl) X =
  cong Fin.suc
    (trans (cong (toRenameᵗ _) (toRename-id-eq X))
      (sym (toRename-id-eq (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀ (target-extend-skipᶜ₀ plan) X =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-lift-bothᶜ₀ plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴿᶜ₀
    (target-extend-lift-bothᶜ₀ plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) X =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) X =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))


extendTarget-marksᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (Z : TyVar (centerᶜ₀ W))
  → marksᶜ₀ (extendTargetᶜ₀ plan)
      (subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi Z))
    ≡ marksᶜ₀ W Z
extendTarget-marksᶜ₀
    (target-extend-starᶜ₀ fresh eqᴿ refl refl) Z
    rewrite toRename-id-eq Z = refl
extendTarget-marksᶜ₀
    (target-extend-aliasᶜ₀ fresh eqᴿ refl refl) Z
    rewrite toRename-id-eq Z = refl
extendTarget-marksᶜ₀ (target-extend-skipᶜ₀ plan) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀ (target-extend-skipᶜ₀ plan) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ₀ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-lift-bothᶜ₀ {v = v} plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-lift-bothᶜ₀ {v = v} plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ v (marksᶜ₀ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ₀ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ₀ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ₀ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)


extendTarget-targetLookupᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ₀ Cᴿ} {Cᴿ⁺ rho Δ⁺}
    {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴿ))
  → lookupStore (Σᵉ Cᴿ⁺) (toRenameᵗ rho X)
    ≡ renameᵗ (toRenameᵗ rho) (lookupStore (Σᵉ Cᴿ) X)
extendTarget-targetLookupᶜ₀
    (target-extend-starᶜ₀ {Σᴿ = Σᴿ} fresh eqᴿ refl refl) X =
  trans
    (cong (lookupStore (store-bind Σᴿ ★)) (toRename-wk-eq X))
    (sym (renameᵗ-wk-eq (lookupStore Σᴿ X)))
extendTarget-targetLookupᶜ₀
    (target-extend-aliasᶜ₀ {Σᴿ = Σᴿ} {Y = Y}
      fresh eqᴿ refl refl) X =
  trans
    (cong (lookupStore (store-bind Σᴿ (＇ Y))) (toRename-wk-eq X))
    (sym (renameᵗ-wk-eq (lookupStore Σᴿ X)))
extendTarget-targetLookupᶜ₀ (target-extend-skipᶜ₀ plan) X =
  extendTarget-targetLookupᶜ₀ plan X
extendTarget-targetLookupᶜ₀
    (target-extend-lift-bothᶜ₀ plan _ _ _) Fin.zero = refl
extendTarget-targetLookupᶜ₀
    (target-extend-lift-bothᶜ₀ {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _)
    (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookupᶜ₀ plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookupᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) X =
  extendTarget-targetLookupᶜ₀ plan X
extendTarget-targetLookupᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) X =
  extendTarget-targetLookupᶜ₀ plan X
extendTarget-targetLookupᶜ₀
    (target-extend-bind-rightᶜ₀ {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookupᶜ₀
    (target-extend-bind-rightᶜ₀ {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookupᶜ₀ plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))


extendTarget-invariantsᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ₀ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ₀ W ↪ᵗ Δ⁺}
  → (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
  → DirectWorldInvariantsᶜ₀ (extendTargetᶜ₀ plan)
extendTarget-invariantsᶜ₀ plan = directInvariantsᶜ₀ (extendTargetᶜ₀ plan)


-- The first relation-indexed obstruction is the paired raw head.  Rebuilding
-- it requires this transport fact from the child plan; neither freshness nor
-- the world invariants imply it.  The next probe step must prove this theorem
-- from the embedding and mark laws, then use it in paired and term heads:
--
--   A ⊑ᵀ₀⟨ W ⟩ B
--     -> A ⊑ᵀ₀⟨ extendTargetᶜ₀ plan ⟩
--          renameᵗ (toRenameᵗ rho) B


star-root-planᶜ₀ : TargetExtendPlanᶜ₀ stable-world
    ⟨ suc (Δᵉ target-alpha-context) ,
      store-bind (Σᵉ target-alpha-context) ★ ,
      TC.⇑ᶜ (Γᵉ target-alpha-context) ⟩
    (skip id↪ᵗ) (skip id↪ᵗ)
star-root-planᶜ₀ = target-extend-starᶜ₀ (inj₁ refl) refl refl refl

alias-root-planᶜ₀ : TargetExtendPlanᶜ₀ stable-world
    target-alpha-beta-context (skip id↪ᵗ) (skip id↪ᵗ)
alias-root-planᶜ₀ =
  target-extend-aliasᶜ₀ (inj₂ (Fin.suc target-alpha , refl , no-source))
    refl refl refl
  where
  no-source : ∀ Xᴸ
    → toRenameᵗ (skip (ηᴸᶜ₀ stable-world)) Xᴸ
      ≢ toRenameᵗ (keep (ηᴿᶜ₀ stable-world))
          (Fin.suc target-alpha)
  no-source Fin.zero ()
