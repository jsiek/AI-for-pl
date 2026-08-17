module proof.TermInTermSubst where

-- File Charter:
--   * Term-variable renaming and substitution properties for GTSFImp terms.
--   * Proves preservation of values and typing under parallel operations.
--   * Derives the single-variable typing substitution theorem used by beta
--     reduction preservation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; _×_; ∃-syntax)

open import Types
open import TyStore
open import TermCtx hiding (_∋_⦂_)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import proof.TypeInTermSubst

------------------------------------------------------------------------
-- Renaming term variables
------------------------------------------------------------------------

rename-preserves-Value : ∀ {Δ} rho {V : Term Δ}
  → Value V
  → Value (rename rho V)
rename-preserves-Value rho (ƛ N) = ƛ _
rename-preserves-Value rho (Λ vV) = Λ (rename-preserves-Value rho vV)
rename-preserves-Value rho ($ κ) = $ κ
rename-preserves-Value rho (vV 《 inj 》) =
  rename-preserves-Value rho vV 《 inj 》
rename-preserves-Value rho (vV 《 fun 》) =
  rename-preserves-Value rho vV 《 fun 》
rename-preserves-Value rho (vV 《 all 》) =
  rename-preserves-Value rho vV 《 all 》
rename-preserves-Value rho (vV 《 genᵥ A≠★ safe 》) =
  rename-preserves-Value rho vV 《 genᵥ A≠★ safe 》
rename-preserves-Value rho (vV ↑ fun) = rename-preserves-Value rho vV ↑ fun
rename-preserves-Value rho (vV ↑ all) = rename-preserves-Value rho vV ↑ all
rename-preserves-Value rho (vV ↓ seal) =
  rename-preserves-Value rho vV ↓ seal
rename-preserves-Value rho (vV ↓ fun) = rename-preserves-Value rho vV ↓ fun
rename-preserves-Value rho (vV ↓ all) = rename-preserves-Value rho vV ↓ all

lookup-shift-inv : ∀ {Δ} {Γ : TermCtx Δ} {x B}
  → TermCtx._∋_⦂_ (⇑ᶜ Γ) x B
  → ∃[ A ] (TermCtx._∋_⦂_ Γ x A × ⇑ᵗ A ≡ B)
lookup-shift-inv {Γ = A ∷ Γ} Z = A , Z , refl
lookup-shift-inv {Γ = C ∷ Γ} (S x∈)
    with lookup-shift-inv x∈
lookup-shift-inv {Γ = C ∷ Γ} (S x∈) | A , A∈ , eq =
  A , S A∈ , eq

RenameWf : ∀ {Δ} → TermCtx Δ → TermCtx Δ → Rename → Set
RenameWf Γ Γ′ rho = ∀ {x A}
  → TermCtx._∋_⦂_ Γ x A
  → TermCtx._∋_⦂_ Γ′ (rho x) A

RenameWf-ext : ∀ {Δ} {Γ Γ′ : TermCtx Δ} {A rho}
  → RenameWf Γ Γ′ rho
  → RenameWf (A ∷ Γ) (A ∷ Γ′) (ext rho)
RenameWf-ext hrho Z = Z
RenameWf-ext hrho (S x∈) = S (hrho x∈)

RenameWf-⇑ᶜ : ∀ {Δ} {Γ Γ′ : TermCtx Δ} {rho}
  → RenameWf Γ Γ′ rho
  → RenameWf (⇑ᶜ Γ) (⇑ᶜ Γ′) rho
RenameWf-⇑ᶜ hrho x∈ with lookup-shift-inv x∈
RenameWf-⇑ᶜ hrho x∈ | A , A∈ , refl =
  renameᵗ-∋ _ (hrho A∈)

typing-rename : ∀ {Δ} {Σ : TyStore Δ} {Γ Γ′ M A rho}
  → RenameWf Γ Γ′ rho
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , Γ′ ⟩ ⊢ rename rho M ⦂ A
typing-rename hrho (⊢` x∈) = ⊢` (hrho x∈)
typing-rename hrho (⊢ƛ M⊢) = ⊢ƛ (typing-rename (RenameWf-ext hrho) M⊢)
typing-rename hrho (⊢· L⊢ M⊢) =
  ⊢· (typing-rename hrho L⊢) (typing-rename hrho M⊢)
typing-rename hrho (⊢Λ vM M⊢) =
  ⊢Λ (rename-preserves-Value _ vM)
    (typing-rename (RenameWf-⇑ᶜ hrho) M⊢)
typing-rename hrho (⊢• L⊢) = ⊢• (typing-rename hrho L⊢)
typing-rename hrho (⊢$ κ) = ⊢$ κ
typing-rename hrho (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (typing-rename hrho L⊢) (typing-rename hrho M⊢)
typing-rename hrho (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (typing-rename hrho M⊢) c
typing-rename hrho (⊢reveal c⊢ M⊢) =
  ⊢reveal c⊢ (typing-rename hrho M⊢)
typing-rename hrho (⊢conceal c⊢ M⊢) =
  ⊢conceal c⊢ (typing-rename hrho M⊢)
typing-rename hrho ⊢blame = ⊢blame

typing-rename-shift : ∀ {Δ} {Σ : TyStore Δ} {Γ M A B}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , B ∷ Γ ⟩ ⊢ rename suc M ⦂ A
typing-rename-shift M⊢ = typing-rename (λ x∈ → S x∈) M⊢

------------------------------------------------------------------------
-- Substituting term variables
------------------------------------------------------------------------

subst-preserves-Value : ∀ {Δ} (sigma : Subst Δ) {V : Term Δ}
  → Value V
  → Value (CastTerms.subst sigma V)
subst-preserves-Value sigma (ƛ N) = ƛ _
subst-preserves-Value sigma (Λ vV) =
  Λ (subst-preserves-Value (liftˢ sigma) vV)
subst-preserves-Value sigma ($ κ) = $ κ
subst-preserves-Value sigma (vV 《 inj 》) =
  subst-preserves-Value sigma vV 《 inj 》
subst-preserves-Value sigma (vV 《 fun 》) =
  subst-preserves-Value sigma vV 《 fun 》
subst-preserves-Value sigma (vV 《 all 》) =
  subst-preserves-Value sigma vV 《 all 》
subst-preserves-Value sigma (vV 《 genᵥ A≠★ safe 》) =
  subst-preserves-Value sigma vV 《 genᵥ A≠★ safe 》
subst-preserves-Value sigma (vV ↑ fun) =
  subst-preserves-Value sigma vV ↑ fun
subst-preserves-Value sigma (vV ↑ all) =
  subst-preserves-Value sigma vV ↑ all
subst-preserves-Value sigma (vV ↓ seal) =
  subst-preserves-Value sigma vV ↓ seal
subst-preserves-Value sigma (vV ↓ fun) =
  subst-preserves-Value sigma vV ↓ fun
subst-preserves-Value sigma (vV ↓ all) =
  subst-preserves-Value sigma vV ↓ all

SubstWf : ∀ (Δ : TyCtx) → TyStore Δ
  → TermCtx Δ → TermCtx Δ → Subst Δ → Set
SubstWf Δ Σ Γ Γ′ sigma = ∀ {x A}
  → TermCtx._∋_⦂_ Γ x A
  → ⟨ Δ , Σ , Γ′ ⟩ ⊢ sigma x ⦂ A

SubstWf-exts : ∀ {Δ} {Σ : TyStore Δ} {Γ Γ′ : TermCtx Δ}
    {A sigma}
  → SubstWf Δ Σ Γ Γ′ sigma
  → SubstWf Δ Σ (A ∷ Γ) (A ∷ Γ′) (exts sigma)
SubstWf-exts hsigma Z = ⊢` Z
SubstWf-exts hsigma (S x∈) = typing-rename-shift (hsigma x∈)

SubstWf-liftˢ : ∀ {Δ} {Σ : TyStore Δ} {Γ Γ′ : TermCtx Δ}
    {sigma}
  → SubstWf Δ Σ Γ Γ′ sigma
  → SubstWf (suc Δ) (store-lift Σ) (⇑ᶜ Γ) (⇑ᶜ Γ′)
      (liftˢ sigma)
SubstWf-liftˢ hsigma x∈ with lookup-shift-inv x∈
SubstWf-liftˢ hsigma x∈ | A , A∈ , refl =
  typing-shiftᵗ-lift (hsigma A∈)

typing-subst : ∀ {Δ} {Σ : TyStore Δ} {Γ Γ′ M A sigma}
  → SubstWf Δ Σ Γ Γ′ sigma
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → ⟨ Δ , Σ , Γ′ ⟩ ⊢ CastTerms.subst sigma M ⦂ A
typing-subst hsigma (⊢` x∈) = hsigma x∈
typing-subst hsigma (⊢ƛ M⊢) =
  ⊢ƛ (typing-subst (SubstWf-exts hsigma) M⊢)
typing-subst hsigma (⊢· L⊢ M⊢) =
  ⊢· (typing-subst hsigma L⊢) (typing-subst hsigma M⊢)
typing-subst hsigma (⊢Λ vM M⊢) =
  ⊢Λ (subst-preserves-Value _ vM)
    (typing-subst (SubstWf-liftˢ hsigma) M⊢)
typing-subst hsigma (⊢• L⊢) = ⊢• (typing-subst hsigma L⊢)
typing-subst hsigma (⊢$ κ) = ⊢$ κ
typing-subst hsigma (⊢⊕ op L⊢ M⊢) =
  ⊢⊕ op (typing-subst hsigma L⊢) (typing-subst hsigma M⊢)
typing-subst hsigma (⊢⟨⟩ M⊢ c) = ⊢⟨⟩ (typing-subst hsigma M⊢) c
typing-subst hsigma (⊢reveal c⊢ M⊢) =
  ⊢reveal c⊢ (typing-subst hsigma M⊢)
typing-subst hsigma (⊢conceal c⊢ M⊢) =
  ⊢conceal c⊢ (typing-subst hsigma M⊢)
typing-subst hsigma ⊢blame = ⊢blame

singleSubstWf : ∀ {Δ} {Σ : TyStore Δ} {Γ A V}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ A
  → SubstWf Δ Σ (A ∷ Γ) Γ (singleSub V)
singleSubstWf V⊢ Z = V⊢
singleSubstWf V⊢ (S x∈) = ⊢` x∈

typing-single-subst : ∀ {Δ} {Σ : TyStore Δ} {Γ N V A B}
  → ⟨ Δ , Σ , A ∷ Γ ⟩ ⊢ N ⦂ B
  → ⟨ Δ , Σ , Γ ⟩ ⊢ V ⦂ A
  → ⟨ Δ , Σ , Γ ⟩ ⊢ N [ V ] ⦂ B
typing-single-subst N⊢ V⊢ = typing-subst (singleSubstWf V⊢) N⊢
