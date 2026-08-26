module proof.LR-narrow.TermSubstitution where

-- File Charter:
--   * Extends the core term-substitution theory for the interpreter LR.
--   * Proves term-substitution fusion through type binders and closed terms.
--   * Depends on LR-local type-renaming composition and function
--     extensionality.

open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_; _×_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)

open import Types
open import TyStore
open import TermCtx hiding (_∋_⦂_)
open import Consistency
open import Conversion
open import Primitives
open import CastTerms
open import proof.TypeInTermSubst
open import proof.LR-narrow.TypeRenamingComposition
  using (shift-square; renameᵗᵐ-square)

------------------------------------------------------------------------
-- Renaming term variables
------------------------------------------------------------------------

ext-cong : ∀ {rho rho′ : Rename}
  → (∀ x → rho x ≡ rho′ x)
  → ∀ x → ext rho x ≡ ext rho′ x
ext-cong eq zero = refl
ext-cong eq (suc x) = cong suc (eq x)

rename-cong : ∀ {Δ} {rho rho′ : Rename}
  → (∀ x → rho x ≡ rho′ x)
  → (M : Term Δ)
  → rename rho M ≡ rename rho′ M
rename-cong eq (` x) = cong CastTerms.`_ (eq x)
rename-cong eq (ƛ M) = cong ƛ_ (rename-cong (ext-cong eq) M)
rename-cong eq (L · M) = cong₂ _·_ (rename-cong eq L) (rename-cong eq M)
rename-cong eq (Λ M) = cong Λ_ (rename-cong eq M)
rename-cong eq (M ⦂∀ C [ A ]) = cong (_⦂∀ C [ A ]) (rename-cong eq M)
rename-cong eq ($ κ) = refl
rename-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (rename-cong eq L) (rename-cong eq M)
rename-cong eq (M ⟨ c ⟩) = cong (_⟨ c ⟩) (rename-cong eq M)
rename-cong eq (M ↑ c) = cong (_↑ c) (rename-cong eq M)
rename-cong eq (M ↓ c) = cong (_↓ c) (rename-cong eq M)
rename-cong eq blame = refl

rename-renameᵗᵐ : ∀ {Δ Δ′} (rho : Rename) (eta : Δ ↪ᵗ Δ′)
  → (M : Term Δ)
  → rename rho (renameᵗᵐ eta M) ≡ renameᵗᵐ eta (rename rho M)
rename-renameᵗᵐ rho eta (` x) = refl
rename-renameᵗᵐ rho eta (ƛ M) =
  cong ƛ_ (rename-renameᵗᵐ (ext rho) eta M)
rename-renameᵗᵐ rho eta (L · M) =
  cong₂ _·_ (rename-renameᵗᵐ rho eta L)
    (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta (Λ M) =
  cong Λ_ (rename-renameᵗᵐ rho (keep eta) M)
rename-renameᵗᵐ rho eta (M ⦂∀ C [ A ]) =
  cong (_⦂∀ renameᵗ (toRenameᵗ (keep eta)) C
    [ renameᵗ (toRenameᵗ eta) A ]) (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta ($ κ) = refl
rename-renameᵗᵐ rho eta (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (rename-renameᵗᵐ rho eta L) (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta (M ⟨ c ⟩) =
  cong (_⟨ renameᵐᶜ eta c ⟩) (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta (M ↑ c) =
  cong (_↑ rename↑ (toRenameᵗ eta) c) (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta (M ↓ c) =
  cong (_↓ rename↓ (toRenameᵗ eta) c) (rename-renameᵗᵐ rho eta M)
rename-renameᵗᵐ rho eta blame = refl

rename-rename : ∀ {Δ} (rho tau : Rename) (M : Term Δ)
  → rename tau (rename rho M) ≡ rename (λ x → tau (rho x)) M
rename-rename rho tau (` x) = refl
rename-rename rho tau (ƛ M) =
  cong ƛ_
    (trans (rename-rename (ext rho) (ext tau) M)
      (rename-cong env-eq M))
  where
  env-eq : ∀ x
    → ext tau (ext rho x) ≡ ext (λ y → tau (rho y)) x
  env-eq zero = refl
  env-eq (suc x) = refl
rename-rename rho tau (L · M) =
  cong₂ _·_ (rename-rename rho tau L) (rename-rename rho tau M)
rename-rename rho tau (Λ M) = cong Λ_ (rename-rename rho tau M)
rename-rename rho tau (M ⦂∀ C [ A ]) =
  cong (_⦂∀ C [ A ]) (rename-rename rho tau M)
rename-rename rho tau ($ κ) = refl
rename-rename rho tau (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (rename-rename rho tau L) (rename-rename rho tau M)
rename-rename rho tau (M ⟨ c ⟩) =
  cong (_⟨ c ⟩) (rename-rename rho tau M)
rename-rename rho tau (M ↑ c) =
  cong (_↑ c) (rename-rename rho tau M)
rename-rename rho tau (M ↓ c) =
  cong (_↓ c) (rename-rename rho tau M)
rename-rename rho tau blame = refl

rename-shift : ∀ {Δ} (rho : Rename) (M : Term Δ)
  → rename (ext rho) (rename suc M) ≡ rename suc (rename rho M)
rename-shift rho M =
  trans (rename-rename suc (ext rho) M)
    (sym (rename-rename rho suc M))

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

exts-cong : ∀ {Δ} {sigma tau : Subst Δ}
  → (∀ x → sigma x ≡ tau x)
  → ∀ x → exts sigma x ≡ exts tau x
exts-cong eq zero = refl
exts-cong eq (suc x) = cong (rename suc) (eq x)

liftˢ-cong : ∀ {Δ} {sigma tau : Subst Δ}
  → (∀ x → sigma x ≡ tau x)
  → ∀ x → liftˢ sigma x ≡ liftˢ tau x
liftˢ-cong eq x = cong ⇑ᵗᵐ (eq x)

subst-cong : ∀ {Δ} {sigma tau : Subst Δ}
  → (∀ x → sigma x ≡ tau x)
  → (M : Term Δ)
  → CastTerms.subst sigma M ≡ CastTerms.subst tau M
subst-cong eq (` x) = eq x
subst-cong eq (ƛ M) = cong ƛ_ (subst-cong (exts-cong eq) M)
subst-cong eq (L · M) = cong₂ _·_ (subst-cong eq L) (subst-cong eq M)
subst-cong eq (Λ M) = cong Λ_ (subst-cong (liftˢ-cong eq) M)
subst-cong eq (M ⦂∀ C [ A ]) = cong (_⦂∀ C [ A ]) (subst-cong eq M)
subst-cong eq ($ κ) = refl
subst-cong eq (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (subst-cong eq L) (subst-cong eq M)
subst-cong eq (M ⟨ c ⟩) = cong (_⟨ c ⟩) (subst-cong eq M)
subst-cong eq (M ↑ c) = cong (_↑ c) (subst-cong eq M)
subst-cong eq (M ↓ c) = cong (_↓ c) (subst-cong eq M)
subst-cong eq blame = refl

subst-rename : ∀ {Δ} (sigma : Subst Δ) (rho : Rename)
  → (M : Term Δ)
  → CastTerms.subst sigma (rename rho M)
    ≡ CastTerms.subst (λ x → sigma (rho x)) M
subst-rename sigma rho (` x) = refl
subst-rename sigma rho (ƛ M) =
  cong ƛ_
    (trans (subst-rename (exts sigma) (ext rho) M)
      (subst-cong env-eq M))
  where
  env-eq : ∀ x
    → exts sigma (ext rho x) ≡ exts (λ y → sigma (rho y)) x
  env-eq zero = refl
  env-eq (suc x) = refl
subst-rename sigma rho (L · M) =
  cong₂ _·_ (subst-rename sigma rho L) (subst-rename sigma rho M)
subst-rename sigma rho (Λ M) =
  cong Λ_
    (trans (subst-rename (liftˢ sigma) rho M)
      (subst-cong (liftˢ-cong (λ x → refl)) M))
subst-rename sigma rho (M ⦂∀ C [ A ]) =
  cong (_⦂∀ C [ A ]) (subst-rename sigma rho M)
subst-rename sigma rho ($ κ) = refl
subst-rename sigma rho (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (subst-rename sigma rho L) (subst-rename sigma rho M)
subst-rename sigma rho (M ⟨ c ⟩) =
  cong (_⟨ c ⟩) (subst-rename sigma rho M)
subst-rename sigma rho (M ↑ c) =
  cong (_↑ c) (subst-rename sigma rho M)
subst-rename sigma rho (M ↓ c) =
  cong (_↓ c) (subst-rename sigma rho M)
subst-rename sigma rho blame = refl

rename-subst : ∀ {Δ} (rho : Rename) (sigma : Subst Δ)
  → (M : Term Δ)
  → rename rho (CastTerms.subst sigma M)
    ≡ CastTerms.subst (λ x → rename rho (sigma x)) M
rename-subst rho sigma (` x) = refl
rename-subst rho sigma (ƛ M) =
  cong ƛ_
    (trans (rename-subst (ext rho) (exts sigma) M)
      (subst-cong env-eq M))
  where
  env-eq : ∀ x
    → rename (ext rho) (exts sigma x)
      ≡ exts (λ y → rename rho (sigma y)) x
  env-eq zero = refl
  env-eq (suc x) = rename-shift rho (sigma x)
rename-subst rho sigma (L · M) =
  cong₂ _·_ (rename-subst rho sigma L) (rename-subst rho sigma M)
rename-subst rho sigma (Λ M) =
  cong Λ_
    (trans (rename-subst rho (liftˢ sigma) M)
      (subst-cong env-eq M))
  where
  env-eq : ∀ x
    → rename rho (liftˢ sigma x)
      ≡ liftˢ (λ y → rename rho (sigma y)) x
  env-eq x = rename-renameᵗᵐ rho wk↪ᵗ (sigma x)
rename-subst rho sigma (M ⦂∀ C [ A ]) =
  cong (_⦂∀ C [ A ]) (rename-subst rho sigma M)
rename-subst rho sigma ($ κ) = refl
rename-subst rho sigma (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (rename-subst rho sigma L) (rename-subst rho sigma M)
rename-subst rho sigma (M ⟨ c ⟩) =
  cong (_⟨ c ⟩) (rename-subst rho sigma M)
rename-subst rho sigma (M ↑ c) =
  cong (_↑ c) (rename-subst rho sigma M)
rename-subst rho sigma (M ↓ c) =
  cong (_↓ c) (rename-subst rho sigma M)
rename-subst rho sigma blame = refl

exts-subst : ∀ {Δ} (sigma tau : Subst Δ) x
  → CastTerms.subst (exts tau) (exts sigma x)
    ≡ exts (λ y → CastTerms.subst tau (sigma y)) x
exts-subst sigma tau zero = refl
exts-subst sigma tau (suc x) =
  trans (subst-rename (exts tau) suc (sigma x))
    (sym (rename-subst suc tau (sigma x)))

subst-renameᵗᵐ : ∀ {Δ Δ′} (rho : Δ ↪ᵗ Δ′)
    (tau : Subst Δ′) (sigma : Subst Δ)
    (M : Term Δ)
  → (∀ x → tau x ≡ renameᵗᵐ rho (sigma x))
  → CastTerms.subst tau (renameᵗᵐ rho M)
    ≡ renameᵗᵐ rho (CastTerms.subst sigma M)
subst-renameᵗᵐ rho tau sigma (` x) env = env x
subst-renameᵗᵐ rho tau sigma (ƛ M) env =
  cong ƛ_ (subst-renameᵗᵐ rho (exts tau) (exts sigma) M ext-env)
  where
  ext-env : ∀ x → exts tau x ≡ renameᵗᵐ rho (exts sigma x)
  ext-env zero = refl
  ext-env (suc x) =
    trans (cong (rename suc) (env x))
      (rename-renameᵗᵐ suc rho (sigma x))
subst-renameᵗᵐ rho tau sigma (L · M) env =
  cong₂ _·_ (subst-renameᵗᵐ rho tau sigma L env)
    (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma (Λ M) env =
  cong Λ_
    (subst-renameᵗᵐ (keep rho) (liftˢ tau) (liftˢ sigma) M
      lift-env)
  where
  lift-env : ∀ x
    → liftˢ tau x ≡ renameᵗᵐ (keep rho) (liftˢ sigma x)
  lift-env x =
    trans (cong ⇑ᵗᵐ (env x))
      (sym (renameᵗᵐ-square (shift-square rho) (sigma x)))
subst-renameᵗᵐ rho tau sigma (M ⦂∀ C [ A ]) env =
  cong (_⦂∀ renameᵗ (toRenameᵗ (keep rho)) C
    [ renameᵗ (toRenameᵗ rho) A ])
    (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma ($ κ) env = refl
subst-renameᵗᵐ rho tau sigma (L ⊕[ op ] M) env =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (subst-renameᵗᵐ rho tau sigma L env)
    (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma (M ⟨ c ⟩) env =
  cong (_⟨ renameᵐᶜ rho c ⟩) (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma (M ↑ c) env =
  cong (_↑ rename↑ (toRenameᵗ rho) c)
    (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma (M ↓ c) env =
  cong (_↓ rename↓ (toRenameᵗ rho) c)
    (subst-renameᵗᵐ rho tau sigma M env)
subst-renameᵗᵐ rho tau sigma blame env = refl

subst-type-shift : ∀ {Δ} (sigma : Subst Δ) (M : Term Δ)
  → CastTerms.subst (liftˢ sigma) (⇑ᵗᵐ M)
    ≡ ⇑ᵗᵐ (CastTerms.subst sigma M)
subst-type-shift sigma M =
  subst-renameᵗᵐ wk↪ᵗ (liftˢ sigma) sigma M (λ x → refl)

liftˢ-subst : ∀ {Δ} (sigma tau : Subst Δ) x
  → CastTerms.subst (liftˢ tau) (liftˢ sigma x)
    ≡ liftˢ (λ y → CastTerms.subst tau (sigma y)) x
liftˢ-subst sigma tau x = subst-type-shift tau (sigma x)

sub-sub : ∀ {Δ} (sigma tau : Subst Δ) (M : Term Δ)
  → CastTerms.subst tau (CastTerms.subst sigma M)
    ≡ CastTerms.subst
      (λ x → CastTerms.subst tau (sigma x)) M
sub-sub sigma tau (` x) = refl
sub-sub sigma tau (ƛ M) =
  cong ƛ_
    (trans (sub-sub (exts sigma) (exts tau) M)
      (subst-cong (exts-subst sigma tau) M))
sub-sub sigma tau (L · M) =
  cong₂ _·_ (sub-sub sigma tau L) (sub-sub sigma tau M)
sub-sub sigma tau (Λ M) =
  cong Λ_
    (trans (sub-sub (liftˢ sigma) (liftˢ tau) M)
      (subst-cong (liftˢ-subst sigma tau) M))
sub-sub sigma tau (M ⦂∀ C [ A ]) =
  cong (_⦂∀ C [ A ]) (sub-sub sigma tau M)
sub-sub sigma tau ($ κ) = refl
sub-sub sigma tau (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′)
    (sub-sub sigma tau L) (sub-sub sigma tau M)
sub-sub sigma tau (M ⟨ c ⟩) = cong (_⟨ c ⟩) (sub-sub sigma tau M)
sub-sub sigma tau (M ↑ c) = cong (_↑ c) (sub-sub sigma tau M)
sub-sub sigma tau (M ↓ c) = cong (_↓ c) (sub-sub sigma tau M)
sub-sub sigma tau blame = refl

subst-id : ∀ {Δ} (M : Term Δ)
  → CastTerms.subst (λ x → ` x) M ≡ M
subst-id (` x) = refl
subst-id (ƛ M) =
  cong ƛ_
    (trans (subst-cong ext-id M) (subst-id M))
  where
  ext-id : ∀ x → exts (λ y → ` y) x ≡ ` x
  ext-id zero = refl
  ext-id (suc x) = refl
subst-id (L · M) = cong₂ _·_ (subst-id L) (subst-id M)
subst-id (Λ M) =
  cong Λ_
    (trans (subst-cong lift-id M) (subst-id M))
  where
  lift-id : ∀ x → liftˢ (λ y → ` y) x ≡ ` x
  lift-id x = refl
subst-id (M ⦂∀ C [ A ]) = cong (_⦂∀ C [ A ]) (subst-id M)
subst-id ($ κ) = refl
subst-id (L ⊕[ op ] M) =
  cong₂ (λ L′ M′ → L′ ⊕[ op ] M′) (subst-id L) (subst-id M)
subst-id (M ⟨ c ⟩) = cong (_⟨ c ⟩) (subst-id M)
subst-id (M ↑ c) = cong (_↑ c) (subst-id M)
subst-id (M ↓ c) = cong (_↓ c) (subst-id M)
subst-id blame = refl

subst-agree-exts : ∀ {Δ} {Γ : TermCtx Δ} {A : Ty Δ}
    {sigma tau : Subst Δ}
  → (∀ {x B} → TermCtx._∋_⦂_ Γ x B → sigma x ≡ tau x)
  → ∀ {x B} → TermCtx._∋_⦂_ (A ∷ Γ) x B
  → exts sigma x ≡ exts tau x
subst-agree-exts agree Z = refl
subst-agree-exts agree (S x∈) = cong (rename suc) (agree x∈)

subst-agree-liftˢ : ∀ {Δ} {Γ : TermCtx Δ}
    {sigma tau : Subst Δ}
  → (∀ {x B} → TermCtx._∋_⦂_ Γ x B → sigma x ≡ tau x)
  → ∀ {x B} → TermCtx._∋_⦂_ (⇑ᶜ Γ) x B
  → liftˢ sigma x ≡ liftˢ tau x
subst-agree-liftˢ agree x∈ with lookup-shift-inv x∈
subst-agree-liftˢ agree x∈ | A , A∈ , refl =
  cong ⇑ᵗᵐ (agree A∈)

subst-typing-cong : ∀ {Δ} {Σ : TyStore Δ} {Γ : TermCtx Δ}
    {M : Term Δ} {A : Ty Δ} {sigma tau : Subst Δ}
  → (∀ {x B} → TermCtx._∋_⦂_ Γ x B → sigma x ≡ tau x)
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ A
  → CastTerms.subst sigma M ≡ CastTerms.subst tau M
subst-typing-cong agree (⊢` x∈) = agree x∈
subst-typing-cong agree (⊢ƛ M⊢) =
  cong ƛ_ (subst-typing-cong (subst-agree-exts agree) M⊢)
subst-typing-cong agree (⊢· L⊢ M⊢) =
  cong₂ _·_ (subst-typing-cong agree L⊢)
    (subst-typing-cong agree M⊢)
subst-typing-cong agree (⊢Λ vM M⊢) =
  cong Λ_ (subst-typing-cong (subst-agree-liftˢ agree) M⊢)
subst-typing-cong {M = L ⦂∀ C [ A ]} agree (⊢• L⊢) =
  cong (_⦂∀ C [ A ]) (subst-typing-cong agree L⊢)
subst-typing-cong agree (⊢$ κ) = refl
subst-typing-cong agree (⊢⊕ op L⊢ M⊢) =
  cong₂ (λ L M → L ⊕[ op ] M) (subst-typing-cong agree L⊢)
    (subst-typing-cong agree M⊢)
subst-typing-cong agree (⊢⟨⟩ M⊢ c) =
  cong (_⟨ c ⟩) (subst-typing-cong agree M⊢)
subst-typing-cong {M = M ↑ c} agree (⊢reveal c⊢ M⊢) =
  cong (_↑ c) (subst-typing-cong agree M⊢)
subst-typing-cong {M = M ↓ c} agree (⊢conceal c⊢ M⊢) =
  cong (_↓ c) (subst-typing-cong agree M⊢)
subst-typing-cong agree ⊢blame = refl

subst-closed : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ} {A : Ty Δ}
  → (sigma : Subst Δ)
  → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ A
  → CastTerms.subst sigma M ≡ M
subst-closed {M = M} sigma M⊢ =
  trans (subst-typing-cong (λ ()) M⊢) (subst-id M)

single-subst-exts : ∀ {Δ} (sigma : Subst Δ) (N V : Term Δ)
  → (CastTerms.subst (exts sigma) N) [ V ]
    ≡ CastTerms.subst
      (λ x → CastTerms.subst (singleSub V) (exts sigma x)) N
single-subst-exts sigma N V = sub-sub (exts sigma) (singleSub V) N

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
