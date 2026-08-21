{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxTargetExtendPlanProbe where

-- File Charter:
--   * Checks structural target insertion over the two-Ctx raw world history.
--   * Starts with explicit fresh right-star or direct-alias insertion and
--     reconstructs skipped, lifted, source-bound, and target-bound heads.
--   * Computes the new world from the plan, derives its invariants from raw
--     history, and proves the center, embedding, mark, and direct-store laws.
--   * Transports type imprecision from those laws and reconstructs paired,
--     paired-star, and term-binding heads through checked smart constructors.

open import Data.Nat using (suc)
open import Data.List using (_∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
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
open import proof.DGG.TwoCtxWorld
open import proof.DGG.TwoCtxWorldInvariants
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
  data TargetExtendPlanᶜ₀ : ∀ {Cᴸ Cᴿ : Ctx}
      → (W : Cᴸ ⊑ᶜ Cᴿ)
      → (Cᴿ⁺ : Ctx)
      → (rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺)
      → ∀ {Δ⁺} → centerᶜ W ↪ᵗ Δ⁺ → Set where

    target-extend-starᶜ₀ :
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
      → TargetExtendPlanᶜ₀ W
          ⟨ suc Δᴿ , store-bind Σᴿ ★ , Γᴿ⁺ ⟩ rho pi

    target-extend-aliasᶜ₀ :
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
      → TargetExtendPlanᶜ₀ W
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ Y) , Γᴿ⁺ ⟩ rho pi

    target-extend-skipᶜ₀ : ∀ {Cᴸ Cᴿ Cᴿ⁺}
        {W : Cᴸ ⊑ᶜ Cᴿ} {rho : Δᵉ Cᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → TargetExtendPlanᶜ₀ (skip-centerᶜ W) Cᴿ⁺ rho (keep pi)

    target-extend-lift-bothᶜ₀ :
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
      → TargetExtendPlanᶜ₀ W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (lift-both-rawᶜ W v Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ , store-lift Σᴿ⁺ , Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-lift-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlanᶜ₀
          (lift-left-rawᶜ W Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-leftᶜ₀ :
      ∀ {Δᴸ Δᴿ} {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴸ¹ : TermCtx (suc Δᴸ)} {A : Ty Δᴸ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {Cᴿ⁺ : Ctx} {rho : Δᴿ ↪ᵗ Δᵉ Cᴿ⁺}
        {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → TargetExtendPlanᶜ₀
          (bind-left-rawᶜ W A Γᴸ≡) Cᴿ⁺ rho (keep pi)

    target-extend-bind-rightᶜ₀ :
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
      → (plan : TargetExtendPlanᶜ₀
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (fresh⁺ : RightBindFreshᶜ (extendTargetᶜ₀ plan)
          (renameᵗ (toRenameᵗ rho) B))
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (bind-right-rawᶜ W B fresh Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-both-rawᶜ₀ :
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
      → (plan : TargetExtendPlanᶜ₀
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTargetᶜ₀ plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (bind-both-rawᶜ W represented Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-both-star-rawᶜ₀ :
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
      → (plan : TargetExtendPlanᶜ₀
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTargetᶜ₀ plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
      → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
      → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
      → TargetExtendPlanᶜ₀
          (bind-both-star-rawᶜ W represented A≢★ Γᴸ≡ Γᴿ≡)
          ⟨ suc Δᴿ⁺ ,
            store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) ,
            Γᴿ⁺¹ ⟩
          (keep rho) (keep pi)

    target-extend-bind-term-rawᶜ₀ :
      ∀ {Δᴸ Δᴿ Δᴿ⁺}
        {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
        {Σᴿ⁺ : TyStore Δᴿ⁺}
        {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
        {Γᴿ⁺ : TermCtx Δᴿ⁺} {A : Ty Δᴸ} {B : Ty Δᴿ}
        {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
        {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
        {represented : A ⊑ᵀ⟨ W ⟩ B}
      → (plan : TargetExtendPlanᶜ₀
          W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
      → (represented⁺ : A ⊑ᵀ⟨ extendTargetᶜ₀ plan ⟩
          renameᵗ (toRenameᵗ rho) B)
      → TargetExtendPlanᶜ₀
          (bind-termᶜ W represented)
          ⟨ Δᴿ⁺ , Σᴿ⁺ ,
            renameᵗ (toRenameᵗ rho) B ∷ Γᴿ⁺ ⟩
          rho pi

  extendTargetᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
      {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    → TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi
    → Cᴸ ⊑ᶜ Cᴿ⁺
  extendTargetᶜ₀ {W = W}
      (target-extend-starᶜ₀ fresh eqᴿ refl refl) =
    bind-right-rawᶜ W ★ fresh eqᴿ
  extendTargetᶜ₀ {W = W}
      (target-extend-aliasᶜ₀ {Y = Y} fresh eqᴿ refl refl) =
    bind-right-rawᶜ W (＇ Y) fresh eqᴿ
  extendTargetᶜ₀ (target-extend-skipᶜ₀ plan) =
    skip-centerᶜ (extendTargetᶜ₀ plan)
  extendTargetᶜ₀
      (target-extend-lift-bothᶜ₀ {v = v} plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    lift-both-rawᶜ (extendTargetᶜ₀ plan) v Γᴸ≡ Γᴿ⁺≡
  extendTargetᶜ₀
      (target-extend-lift-leftᶜ₀ plan Γᴸ≡) =
    lift-left-rawᶜ (extendTargetᶜ₀ plan) Γᴸ≡
  extendTargetᶜ₀
      (target-extend-bind-leftᶜ₀ {A = A} plan Γᴸ≡) =
    bind-left-rawᶜ (extendTargetᶜ₀ plan) A Γᴸ≡
  extendTargetᶜ₀
      (target-extend-bind-rightᶜ₀ {B = B}
        plan fresh⁺ Γᴿ≡ Γᴿ⁺≡) =
    bind-right-rawᶜ (extendTargetᶜ₀ plan)
      (renameᵗ (toRenameᵗ _) B) fresh⁺ Γᴿ⁺≡
  extendTargetᶜ₀
      (target-extend-bind-both-rawᶜ₀
        plan represented⁺ Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    bind-both-rawᶜ (extendTargetᶜ₀ plan) represented⁺ Γᴸ≡ Γᴿ⁺≡
  extendTargetᶜ₀
      (target-extend-bind-both-star-rawᶜ₀
        {A≢★ = A≢★} plan represented⁺ Γᴸ≡ Γᴿ≡ Γᴿ⁺≡) =
    bind-both-star-rawᶜ (extendTargetᶜ₀ plan) represented⁺ A≢★
      Γᴸ≡ Γᴿ⁺≡
  extendTargetᶜ₀
      (target-extend-bind-term-rawᶜ₀ plan represented⁺) =
    bind-termᶜ (extendTargetᶜ₀ plan) represented⁺


extendTarget-centerᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
  → centerᶜ (extendTargetᶜ₀ plan) ≡ Δ⁺
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
extendTarget-centerᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _) =
  cong suc (extendTarget-centerᶜ₀ plan)
extendTarget-centerᶜ₀
    (target-extend-bind-term-rawᶜ₀ plan _) =
  extendTarget-centerᶜ₀ plan


extendTarget-ηᴸᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴸ))
  → toRenameᵗ (ηᴸᶜ (extendTargetᶜ₀ plan)) X
    ≡ subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴸᶜ W) X))
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
extendTarget-ηᴸᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _)
    (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴸᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴸᶜ₀
    (target-extend-bind-term-rawᶜ₀ plan _) X =
  extendTarget-ηᴸᶜ₀ plan X


extendTarget-ηᴿᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (X : TyVar (Δᵉ Cᴿ))
  → toRenameᵗ (ηᴿᶜ (extendTargetᶜ₀ plan))
      (toRenameᵗ rho X)
    ≡ subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi (toRenameᵗ (ηᴿᶜ W) X))
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
extendTarget-ηᴿᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _) Fin.zero =
  sym (subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _)
    (Fin.suc X) =
  trans (cong Fin.suc (extendTarget-ηᴿᶜ₀ plan X))
    (sym (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
      (toRenameᵗ _ (toRenameᵗ _ X))))
extendTarget-ηᴿᶜ₀
    (target-extend-bind-term-rawᶜ₀ plan _) X =
  extendTarget-ηᴿᶜ₀ plan X


extendTarget-marksᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
    (Z : TyVar (centerᶜ W))
  → marksᶜ (extendTargetᶜ₀ plan)
      (subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
        (toRenameᵗ pi Z))
    ≡ marksᶜ W Z
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
        (cong (extendᵐ X⊑★ (marksᶜ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-lift-bothᶜ₀ {v = v} plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-lift-bothᶜ₀ {v = v} plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ v (marksᶜ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-lift-leftᶜ₀ plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-leftᶜ₀ plan _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-rightᶜ₀ plan _ _ _) (Fin.suc Z)
    = trans
        (cong (extendᵐ X⊑★ (marksᶜ (extendTargetᶜ₀ plan)))
          (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
            (toRenameᵗ _ Z)))
        (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-both-rawᶜ₀ plan _ _ _ _) (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑X (marksᶜ (extendTargetᶜ₀ plan)))
      (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
        (toRenameᵗ _ Z)))
    (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _) Fin.zero
    rewrite subst-Fin-zero-sym (extendTarget-centerᶜ₀ plan) = refl
extendTarget-marksᶜ₀
    (target-extend-bind-both-star-rawᶜ₀ plan _ _ _ _)
    (Fin.suc Z) =
  trans
    (cong (extendᵐ X⊑★ (marksᶜ (extendTargetᶜ₀ plan)))
      (subst-Fin-suc-sym (extendTarget-centerᶜ₀ plan)
        (toRenameᵗ _ Z)))
    (extendTarget-marksᶜ₀ plan Z)
extendTarget-marksᶜ₀
    (target-extend-bind-term-rawᶜ₀ plan _) Z =
  extendTarget-marksᶜ₀ plan Z


extendTarget-targetLookupᶜ₀ : ∀ {Cᴸ Cᴿ}
    {W : Cᴸ ⊑ᶜ Cᴿ} {Cᴿ⁺ rho Δ⁺}
    {pi : centerᶜ W ↪ᵗ Δ⁺}
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
extendTarget-targetLookupᶜ₀
    (target-extend-bind-both-rawᶜ₀
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookupᶜ₀
    (target-extend-bind-both-rawᶜ₀
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookupᶜ₀ plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookupᶜ₀
    (target-extend-bind-both-star-rawᶜ₀
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) Fin.zero =
  sym (renameᵗ-keep-shift rho _)
extendTarget-targetLookupᶜ₀
    (target-extend-bind-both-star-rawᶜ₀
      {Σᴿ = Σᴿ} {rho = rho} plan _ _ _ _) (Fin.suc X) =
  trans
    (cong ⇑ᵗ (extendTarget-targetLookupᶜ₀ plan X))
    (sym (renameᵗ-keep-shift rho (lookupStore Σᴿ X)))
extendTarget-targetLookupᶜ₀
    (target-extend-bind-term-rawᶜ₀ plan _) X =
  extendTarget-targetLookupᶜ₀ plan X


extendTarget-⊑ᵀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
    {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ Cᴿ)}
    (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
  → A ⊑ᵀ⟨ W ⟩ B
  → A ⊑ᵀ⟨ extendTargetᶜ₀ plan ⟩
      renameᵗ (toRenameᵗ rho) B
extendTarget-⊑ᵀ {W = W} {rho = rho} {pi = pi}
    {A = A} {B = B} plan represented =
  subst
    (λ L → marksᶜ (extendTargetᶜ₀ plan) ⊢ L ⊑
      renameᵗ (toRenameᵗ (ηᴿᶜ (extendTargetᶜ₀ plan)))
        (renameᵗ (toRenameᵗ rho) B))
    (sym source-eq)
    (subst
      (λ R → marksᶜ (extendTargetᶜ₀ plan) ⊢
        renameᵗ center-map
          (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A) ⊑ R)
      (sym target-eq)
      (rename-⊑ center-map center-map-injective star-map represented))
  where
  center-map : TyVar (centerᶜ W)
    → TyVar (centerᶜ (extendTargetᶜ₀ plan))
  center-map Z =
    subst Fin.Fin (sym (extendTarget-centerᶜ₀ plan))
      (toRenameᵗ pi Z)

  center-map-injective : ∀ {Y Z}
    → center-map Y ≡ center-map Z
    → Y ≡ Z
  center-map-injective eq =
    toRenameᵗ-injective pi
      (subst-Fin-sym-injective (extendTarget-centerᶜ₀ plan) eq)

  star-map : ∀ Z
    → marksᶜ W Z ≡ X⊑★
    → marksᶜ (extendTargetᶜ₀ plan) (center-map Z) ≡ X⊑★
  star-map Z mark = trans (extendTarget-marksᶜ₀ plan Z) mark

  source-eq :
      renameᵗ (toRenameᵗ (ηᴸᶜ (extendTargetᶜ₀ plan))) A
    ≡ renameᵗ center-map
        (renameᵗ (toRenameᵗ (ηᴸᶜ W)) A)
  source-eq =
    trans (renameᵗ-cong A (extendTarget-ηᴸᶜ₀ plan))
      (sym (renameᵗ-comp (toRenameᵗ (ηᴸᶜ W)) center-map A))

  target-eq :
      renameᵗ (toRenameᵗ (ηᴿᶜ (extendTargetᶜ₀ plan)))
        (renameᵗ (toRenameᵗ rho) B)
    ≡ renameᵗ center-map
        (renameᵗ (toRenameᵗ (ηᴿᶜ W)) B)
  target-eq =
    trans
      (renameᵗ-comp (toRenameᵗ rho)
        (toRenameᵗ (ηᴿᶜ (extendTargetᶜ₀ plan))) B)
      (trans (renameᵗ-cong B (extendTarget-ηᴿᶜ₀ plan))
        (sym (renameᵗ-comp (toRenameᵗ (ηᴿᶜ W)) center-map B)))


target-extend-bind-bothᶜ₀ :
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
  → (plan : TargetExtendPlanᶜ₀
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
  → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
  → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
  → TargetExtendPlanᶜ₀
      (bind-both-rawᶜ W represented Γᴸ≡ Γᴿ≡)
      ⟨ suc Δᴿ⁺ ,
        store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) , Γᴿ⁺¹ ⟩
      (keep rho) (keep pi)
target-extend-bind-bothᶜ₀ {represented = represented}
    plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡ =
  target-extend-bind-both-rawᶜ₀ plan
    (extendTarget-⊑ᵀ plan represented) Γᴸ≡ Γᴿ≡ Γᴿ⁺≡


target-extend-bind-both-starᶜ₀ :
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
  → (plan : TargetExtendPlanᶜ₀
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → (Γᴸ≡ : Γᴸ¹ ≡ TC.⇑ᶜ Γᴸ)
  → (Γᴿ≡ : Γᴿ¹ ≡ TC.⇑ᶜ Γᴿ)
  → (Γᴿ⁺≡ : Γᴿ⁺¹ ≡ TC.⇑ᶜ Γᴿ⁺)
  → TargetExtendPlanᶜ₀
      (bind-both-star-rawᶜ W represented A≢★ Γᴸ≡ Γᴿ≡)
      ⟨ suc Δᴿ⁺ ,
        store-bind Σᴿ⁺ (renameᵗ (toRenameᵗ rho) B) , Γᴿ⁺¹ ⟩
      (keep rho) (keep pi)
target-extend-bind-both-starᶜ₀ {represented = represented}
    plan Γᴸ≡ Γᴿ≡ Γᴿ⁺≡ =
  target-extend-bind-both-star-rawᶜ₀ plan
    (extendTarget-⊑ᵀ plan represented) Γᴸ≡ Γᴿ≡ Γᴿ⁺≡


target-extend-bind-termᶜ₀ :
    ∀ {Δᴸ Δᴿ Δᴿ⁺}
      {Σᴸ : TyStore Δᴸ} {Σᴿ : TyStore Δᴿ}
      {Σᴿ⁺ : TyStore Δᴿ⁺}
      {Γᴸ : TermCtx Δᴸ} {Γᴿ : TermCtx Δᴿ}
      {Γᴿ⁺ : TermCtx Δᴿ⁺} {A : Ty Δᴸ} {B : Ty Δᴿ}
      {W : ⟨ Δᴸ , Σᴸ , Γᴸ ⟩ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
      {rho : Δᴿ ↪ᵗ Δᴿ⁺} {Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
      {represented : A ⊑ᵀ⟨ W ⟩ B}
  → (plan : TargetExtendPlanᶜ₀
      W ⟨ Δᴿ⁺ , Σᴿ⁺ , Γᴿ⁺ ⟩ rho pi)
  → TargetExtendPlanᶜ₀
      (bind-termᶜ W represented)
      ⟨ Δᴿ⁺ , Σᴿ⁺ , renameᵗ (toRenameᵗ rho) B ∷ Γᴿ⁺ ⟩
      rho pi
target-extend-bind-termᶜ₀ {represented = represented} plan =
  target-extend-bind-term-rawᶜ₀ plan
    (extendTarget-⊑ᵀ plan represented)


extendTarget-invariantsᶜ₀ : ∀ {Cᴸ Cᴿ} {W : Cᴸ ⊑ᶜ Cᴿ}
    {Cᴿ⁺ rho Δ⁺} {pi : centerᶜ W ↪ᵗ Δ⁺}
  → (plan : TargetExtendPlanᶜ₀ W Cᴿ⁺ rho pi)
  → DirectWorldInvariantsᶜ (extendTargetᶜ₀ plan)
extendTarget-invariantsᶜ₀ plan = directInvariantsᶜ (extendTargetᶜ₀ plan)


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
    → toRenameᵗ (skip (ηᴸᶜ stable-world)) Xᴸ
      ≢ toRenameᵗ (keep (ηᴿᶜ stable-world))
          (Fin.suc target-alpha)
  no-source Fin.zero ()
