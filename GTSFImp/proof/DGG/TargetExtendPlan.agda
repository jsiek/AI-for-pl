{-# OPTIONS --safe #-}

module proof.DGG.TargetExtendPlan where

-- File Charter:
--   * Defines structural target insertion over the two-Ctx raw world history.
--   * Starts with explicit fresh right-star or direct-alias insertion and
--     reconstructs skipped, lifted, source-bound, and target-bound heads.
--   * Computes the new world from the plan, derives its invariants from raw
--     history, and proves the center, embedding, mark, and direct-store laws.
--   * Transports type imprecision from those laws and reconstructs paired,
--     paired-star, and term-binding heads through checked smart constructors.
--   * Primary exports are TargetExtendPlan, extendTarget, and their structural
--     laws; dependencies are the canonical two-Ctx world and direct invariants.

open import Data.Nat using (suc)
open import Data.List using (_∷_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong; sym; trans; subst)

open import Types using
  (Ty; TyVar; ★; ＇_; ⇑ᵗ; renameᵗ; renameᵗ-cong; renameᵗ-shift;
   renameᵗ-comp)
open import TyStore using
  (TyStore; lookupStore; store-lift; store-bind)
import TermCtx as TC
open TC using (TermCtx)
open import Consistency using
  (_↪ᵗ_; keep; skip; id↪ᵗ; toRenameᵗ)
open import Imprecision using
  (ImpEnv; VarImp; X⊑X; X⊑★; extendᵐ; _⊢_⊑_)
open import CastTerms using (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; Γᵉ)
open import proof.TypeInTermSubst using
  (toRename-id-eq; toRename-wk-eq; toRename-keep-eq; renameᵗ-wk-eq)
open import proof.ImprecisionConsistency using
  (rename-⊑; toRenameᵗ-injective)
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

  subst-Fin-sym-injective : ∀ {m n} (eq : m ≡ n)
      {X Y : Fin.Fin n}
    → subst Fin.Fin (sym eq) X ≡ subst Fin.Fin (sym eq) Y
    → X ≡ Y
  subst-Fin-sym-injective refl X≡Y = X≡Y

  renameᵗ-keep-shift : ∀ {Δ₀ Δ} (ρ : Δ₀ ↪ᵗ Δ) (A : Ty Δ₀)
    → renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
  renameᵗ-keep-shift ρ A =
    trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)


mutual
  data TargetExtendPlan : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cᴿ)
      → (Cᴿ⁺ : Ctx)
      → (rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺)
      → ∀ {Δ⁺} → centerᶜ W ↪ᵗ Δ⁺ → Set where

    target-extend-star :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ suc Δᴿ}
        {pi : centerᶜ W ↪ᵗ suc (centerᶜ W)}
      → (fresh : RightBindFreshᶜ W ★)
      → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → rho ≡ skip id↪ᵗ
      → pi ≡ skip id↪ᵗ
      → TargetExtendPlan W
          ⟨ suc Δᴿ , store-bind Σᴿ ★ , Γᴿ⁺ ⟩ rho pi

    target-extend-alias :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx (suc Δᴿ)} {Y : TyVar Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ suc Δᴿ}
        {pi : centerᶜ W ↪ᵗ suc (centerᶜ W)}
      → (fresh : RightBindFreshᶜ W (＇ Y))
      → (eqᴿ : Γᴿ⁺ ≡ TC.⇑ᶜ Γᴿ)
      → rho ≡ skip id↪ᵗ
      → pi ≡ skip id↪ᵗ
      → TargetExtendPlan W
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ Y) , Γᴿ⁺ ⟩ rho pi

    target-extend-skip : ∀ {Cᴸ Cᴿ Cᴿ⁺}
        {W : Cᴸ ⊑ᶜ Cᴿ} {rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlan W Cᴿ⁺ rho pi
      → TargetExtendPlan (skip-centerᶜ W) Cᴿ⁺ rho (keep pi)

    target-extend-lift-both :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {v : VarImp}
      → TargetExtendPlan W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlan
          (lift-both-rawᶜ W v Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ , store-lift Σᴿ⁺ , Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-lift-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlan W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlan
          (lift-left-rawᶜ W Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-left :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlan W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlan
          (bind-left-rawᶜ W A Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-right :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {fresh : RightBindFreshᶜ W B}
      → (plan : TargetExtendPlan
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (fresh⁺ : RightBindFreshᶜ (extendTarget plan)
          (renameᵗ (toRenameᵗ rho) B))
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlan
          (bind-right-rawᶜ W B fresh Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-both-raw :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : TargetExtendPlan
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTarget plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlan
          (bind-both-rawᶜ W represented Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-both-star-raw :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
        {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {represented : A ⊑ᵀ⟨ W ⟩ B} {A≢★ : ⇑ᵗ A ≢ ★}
      → (plan : TargetExtendPlan
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTarget plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlan
          (bind-both-star-rawᶜ W represented A≢★ Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-term-raw :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺} {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : TargetExtendPlan
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTarget plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → TargetExtendPlan
          (bind-termᶜ W represented)
          ⟨ Δᴿ⁺ , Σᴿ⁺ ,
            renameᵗ (toRenameᵗ rho) B ∷ Γᴿ⁺ ⟩
          rho pi

  extendTarget : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
      {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    → TargetExtendPlan W Cᴿ⁺ rho pi
    → Cᴸ ⊑ᶜ Cᴿ⁺
  extendTarget {W = W}
      (target-extend-star fresh eqᴿ refl refl) =
    bind-right-rawᶜ W ★ fresh eqᴿ
  extendTarget {W = W}
      (target-extend-alias {Y = Y} fresh eqᴿ refl refl) =
    bind-right-rawᶜ W (＇ Y) fresh eqᴿ
  extendTarget (target-extend-skip plan) =
    skip-centerᶜ (extendTarget plan)
  extendTarget
      (target-extend-lift-both {v = v} plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    lift-both-rawᶜ (extendTarget plan) v Γᴸ≡ Γᴿ⁺≡
  extendTarget
      (target-extend-lift-left plan Γᴸ≡) =
    lift-left-rawᶜ (extendTarget plan) Γᴸ≡
  extendTarget
      (target-extend-bind-left {A = A} plan Γᴸ≡) =
    bind-left-rawᶜ (extendTarget plan) A Γᴸ≡
  extendTarget
      (target-extend-bind-right {B = B}
        plan fresh⁺ Γᴿ≡ Γᴿ⁺≡) =
    bind-right-rawᶜ (extendTarget plan)
      (renameᵗ (toRenameᵗ _) B) fresh⁺ Γᴿ⁺≡
  extendTarget
      (target-extend-bind-both-raw
        plan represented⁺ Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    bind-both-rawᶜ (extendTarget plan) represented⁺ Γᴸ≡ Γᴿ⁺≡
  extendTarget
      (target-extend-bind-both-star-raw
        {A≢★ = A≢★} plan represented⁺ Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    bind-both-star-rawᶜ (extendTarget plan) represented⁺ A≢★
      Γᴸ≡ Γᴿ⁺≡
  extendTarget
      (target-extend-bind-term-raw plan represented⁺) =
    bind-termᶜ (extendTarget plan) represented⁺


extendTarget-center : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
  → centerᶜ (extendTarget plan) ≡ Δ⁺
extendTarget-center (target-extend-star fresh eqᴿ refl refl) = refl
extendTarget-center (target-extend-alias fresh eqᴿ refl refl) = refl
extendTarget-center (target-extend-skip plan) =
  cong suc (extendTarget-center plan)
extendTarget-center (target-extend-lift-both plan _ _ _) =
  cong suc (extendTarget-center plan)
extendTarget-center (target-extend-lift-left plan _) =
  cong suc (extendTarget-center plan)
extendTarget-center (target-extend-bind-left plan _) =
  cong suc (extendTarget-center plan)
extendTarget-center (target-extend-bind-right plan _ _ _) =
  cong suc (extendTarget-center plan)
extendTarget-center
    (target-extend-bind-both-raw plan _ _ _ _) =
  cong suc (extendTarget-center plan)
extendTarget-center
    (target-extend-bind-both-star-raw plan _ _ _ _) =
  cong suc (extendTarget-center plan)
extendTarget-center
    (target-extend-bind-term-raw plan _) =
  extendTarget-center plan


extendTarget-ηᴸ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (extendTarget plan)) X
    ≡ subst Fin.Fin (sym (extendTarget-center plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴸᶜ W) X))
extendTarget-ηᴸ
    (target-extend-star fresh eqᴿ refl refl) X =
  cong Fin.suc (sym (toRename-id-eq (toRenameᵗ _ X)))
extendTarget-ηᴸ
    (target-extend-alias fresh eqᴿ refl refl) X =
  cong Fin.suc (sym (toRename-id-eq (toRenameᵗ _ X)))
extendTarget-ηᴸ (target-extend-skip plan) X =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-lift-both plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴸ
    (target-extend-lift-both plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-lift-left plan _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴸ
    (target-extend-lift-left plan _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-bind-left plan _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴸ
    (target-extend-bind-left plan _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-bind-right plan _ _ _) X =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-bind-both-raw plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴸ
    (target-extend-bind-both-raw plan _ _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-bind-both-star-raw plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴸ
    (target-extend-bind-both-star-raw plan _ _ _ _)
    (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸ
    (target-extend-bind-term-raw plan _) X =
  extendTarget-ηᴸ plan X


extendTarget-ηᴿ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (extendTarget plan))
      (toRenameᵗ rho X)
    ≡ subst Fin.Fin (sym (extendTarget-center plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴿᶜ W) X))
extendTarget-ηᴿ
    (target-extend-star fresh eqᴿ refl refl) X =
  cong Fin.suc
    (trans (cong (toRenameᵗ _) (toRename-id-eq X))
      (sym (toRename-id-eq (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-alias fresh eqᴿ refl refl) X =
  cong Fin.suc
    (trans (cong (toRenameᵗ _) (toRename-id-eq X))
      (sym (toRename-id-eq (toRenameᵗ _ X))))
extendTarget-ηᴿ (target-extend-skip plan) X =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-lift-both plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴿ
    (target-extend-lift-both plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-lift-left plan _) X =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-bind-left plan _) X =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-bind-right plan _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴿ
    (target-extend-bind-right plan _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-bind-both-raw plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴿ
    (target-extend-bind-both-raw plan _ _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-bind-both-star-raw plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-center plan))
extendTarget-ηᴿ
    (target-extend-bind-both-star-raw plan _ _ _ _)
    (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-center plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿ
    (target-extend-bind-term-raw plan _) X =
  extendTarget-ηᴿ plan X


extendTarget-marks : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (extendTarget plan)
      (subst Fin.Fin (sym (extendTarget-center plan))
        (toRenameᵗ pi Z))
    ≡ marksᶜ W Z
extendTarget-marks
    (target-extend-star fresh eqᴿ refl refl) Z
    rewrite toRename-id-eq Z = refl
extendTarget-marks
    (target-extend-alias fresh eqᴿ refl refl) Z
    rewrite toRename-id-eq Z = refl
extendTarget-marks (target-extend-skip plan) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks (target-extend-skip plan) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTarget plan)))
          (subst-Fin-suc-sym (extendTarget-center plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-lift-both {v = v} plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-lift-both {v = v} plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ v (marksᶜ (extendTarget plan)))
          (subst-Fin-suc-sym (extendTarget-center plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-lift-left plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-lift-left plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTarget plan)))
          (subst-Fin-suc-sym (extendTarget-center plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-bind-left plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-bind-left plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTarget plan)))
          (subst-Fin-suc-sym (extendTarget-center plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-bind-right plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-bind-right plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTarget plan)))
          (subst-Fin-suc-sym (extendTarget-center plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-bind-both-raw plan _ _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-bind-both-raw plan _ _ _ _) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑X (marksᶜ (extendTarget plan)))
      (subst-Fin-suc-sym (extendTarget-center plan)
        (toRenameᵗ _ Z)))
    (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-bind-both-star-raw plan _ _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-center plan) = refl
extendTarget-marks
    (target-extend-bind-both-star-raw plan _ _ _ _)
    (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (extendTarget plan)))
      (subst-Fin-suc-sym (extendTarget-center plan)
        (toRenameᵗ _ Z)))
    (extendTarget-marks plan Z)
extendTarget-marks
    (target-extend-bind-term-raw plan _) Z =
  extendTarget-marks plan Z


extendTarget-targetLookup : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Cᴿ⁺ rho Δ⁺}
    {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴿ))
  → lookupStore (Σᵉ Cᴿ⁺) (toRenameᵗ rho X)
    ≡ renameᵗ (toRenameᵗ rho) (lookupStore (Σᵉ Cᴿ) X)
extendTarget-targetLookup
    (target-extend-star {Σᴿ = Σᴿ} fresh eqᴿ refl refl) X =
  trans
    (cong (lookupStore (store-bind Σᴿ ★)) (toRename-wk-eq X))
    (sym (renameᵗ-wk-eq (lookupStore Σᴿ X)))
extendTarget-targetLookup
    (target-extend-alias {Σᴿ = Σᴿ} {Y = Y}
      fresh eqᴿ refl refl) X =
  trans
    (cong (lookupStore (store-bind Σᴿ (＇ Y))) (toRename-wk-eq X))
    (sym (renameᵗ-wk-eq (lookupStore Σᴿ X)))
extendTarget-targetLookup (target-extend-skip plan) X =
  extendTarget-targetLookup plan X
extendTarget-targetLookup
    (target-extend-lift-both plan _ _ _) Fin.zero = refl
extendTarget-targetLookup
    (target-extend-lift-both {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _)
    (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookup plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookup
    (target-extend-lift-left plan _) X =
  extendTarget-targetLookup plan X
extendTarget-targetLookup
    (target-extend-bind-left plan _) X =
  extendTarget-targetLookup plan X
extendTarget-targetLookup
    (target-extend-bind-right {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookup
    (target-extend-bind-right {Σᴿ = Σᴿ} {rho = rho}
      plan _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookup plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookup
    (target-extend-bind-both-raw
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookup
    (target-extend-bind-both-raw
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookup plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookup
    (target-extend-bind-both-star-raw
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookup
    (target-extend-bind-both-star-raw
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookup plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookup
    (target-extend-bind-term-raw plan _) X =
  extendTarget-targetLookup plan X


extendTarget-⊑ᵀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
  → A ⊑ᵀ⟨ W ⟩ B
  → A ⊑ᵀ⟨ extendTarget plan ⟩
      renameᵗ (toRenameᵗ rho) B
extendTarget-⊑ᵀ {W = W} {rho = rho} {pi = pi}
    {A = A} {B = B} plan represented =
  subst
    (λ L → marksᶜ (extendTarget plan) ⊢ L ⊑
      renameᵗ (toRenameᵗ (ηᴿᶜ (extendTarget plan)))
        (renameᵗ (toRenameᵗ rho) B))
    (sym source-eq)
    (subst
      (λ R → marksᶜ (extendTarget plan) ⊢
        renameᵗ center-map
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) ⊑ R)
      (sym target-eq)
      (rename-⊑ center-map center-map-injective star-map represented))
  where
  center-map : TyVar (centerᶜ W)
    → TyVar (centerᶜ (extendTarget plan))
  center-map Z =
    subst Fin.Fin (sym (extendTarget-center plan))
      (toRenameᵗ pi Z)

  center-map-injective : ∀ {Y Z}
    → center-map Y ≡ center-map Z
    → Y ≡ Z
  center-map-injective eq =
    toRenameᵗ-injective pi
      (subst-Fin-sym-injective (extendTarget-center plan) eq)

  star-map : ∀ Z
    → marksᶜ W Z ≡ X⊑★
    → marksᶜ (extendTarget plan) (center-map Z) ≡ X⊑★
  star-map Z mark = trans (extendTarget-marks plan Z) mark

  source-eq :
      renameᵗ (toRenameᵗ (ηᴸᶜ (extendTarget plan))) A
    ≡ renameᵗ center-map
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A)
  source-eq =
    trans (renameᵗ-cong A (extendTarget-ηᴸ plan))
      (sym (renameᵗ-comp (toRenameᵗ (ηᴸᶜ W)) center-map A))

  target-eq :
      renameᵗ (toRenameᵗ (ηᴿᶜ (extendTarget plan)))
        (renameᵗ (toRenameᵗ rho) B)
    ≡ renameᵗ center-map
        (renameᵗ (toRenameᵗ (ηᴿᶜ W)) B)
  target-eq =
    trans
      (renameᵗ-comp (toRenameᵗ rho)
        (toRenameᵗ (ηᴿᶜ (extendTarget plan))) B)
      (trans (renameᵗ-cong B (extendTarget-ηᴿ plan))
        (sym (renameᵗ-comp (toRenameᵗ (ηᴿᶜ W)) center-map B)))


target-extend-bind-both :
    ∀ {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
      {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
  → (plan : TargetExtendPlan
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
  → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
  → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
  → TargetExtendPlan
      (bind-both-rawᶜ W represented Γᴸ≡ Γᴿ≡)
      ⟨ suc Δᴿ⁺ ,
        store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) , Γᴿ⁺¹ ⟩
      (keep rho) (keep pi)
target-extend-bind-both {represented = represented}
    plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡ =
  target-extend-bind-both-raw plan
    (extendTarget-⊑ᵀ plan represented) Γᴸ≡ Γᴿ≡ Γᴿ⁺≡


target-extend-bind-both-star :
    ∀ {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx Δᴿ⁺}
      {Γᴸ¹ : TermCtx (suc Δᴸ)} {Γᴿ¹ : TermCtx (suc Δᴿ)}
      {Γᴿ⁺¹ : TermCtx (suc Δᴿ⁺)}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      {represented : A ⊑ᵀ⟨ W ⟩ B} {A≢★ : ⇑ᵗ A ≢ ★}
  → (plan : TargetExtendPlan
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
  → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
  → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
  → TargetExtendPlan
      (bind-both-star-rawᶜ W represented A≢★ Γᴸ≡ Γᴿ≡)
      ⟨ suc Δᴿ⁺ ,
        store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) , Γᴿ⁺¹ ⟩
      (keep rho) (keep pi)
target-extend-bind-both-star {represented = represented}
    plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡ =
  target-extend-bind-both-star-raw plan
    (extendTarget-⊑ᵀ plan represented) Γᴸ≡ Γᴿ≡ Γᴿ⁺≡


target-extend-bind-term :
    ∀ {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx Δᴿ⁺} {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
  → (plan : TargetExtendPlan
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → TargetExtendPlan
      (bind-termᶜ W represented)
      ⟨ Δᴿ⁺ , Σᴿ⁺ , renameᵗ (toRenameᵗ rho) B ∷ Γᴿ⁺ ⟩
      rho pi
target-extend-bind-term {represented = represented} plan =
  target-extend-bind-term-raw plan
    (extendTarget-⊑ᵀ plan represented)


extendTarget-invariants : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
  → (plan : TargetExtendPlan W Cᴿ⁺ rho pi)
  → DirectWorldInvariantsᶜ (extendTarget plan)
extendTarget-invariants plan = directInvariantsᶜ (extendTarget plan)
