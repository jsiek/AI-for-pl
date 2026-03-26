module TypeSubst where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types

------------------------------------------------------------------------
-- Public API: lemmas used by intrinsic imprecision
------------------------------------------------------------------------
renameᵗ-ground : ∀{Δ Δ′}{Ψ}{G : Ty Δ Ψ} (ρ : Renameᵗ Δ Δ′)
  → Ground G
  → Ground (renameᵗ ρ G)
renameᵗ-ground ρ (｀ α) = ｀ α
renameᵗ-ground ρ (‵ ι) = ‵ ι
renameᵗ-ground ρ ★⇒★ = ★⇒★

substᵗ-ground : ∀{Δ Δ′}{Ψ}{G : Ty Δ Ψ} (ρ : Substᵗ Δ Δ′ Ψ)
  → Ground G
  → Ground (substᵗ ρ G)
substᵗ-ground ρ (｀ α) = ｀ α
substᵗ-ground ρ (‵ ι) = ‵ ι
substᵗ-ground ρ ★⇒★ = ★⇒★

renameˢ-ground : ∀{Δ}{Ψ Ψ′}{G : Ty Δ Ψ} (ρ : Renameˢ Ψ Ψ′)
  → Ground G
  → Ground (renameˢ ρ G)
renameˢ-ground ρ (｀ α) = ｀ (ρ α)
renameˢ-ground ρ (‵ ι) = ‵ ι
renameˢ-ground ρ ★⇒★ = ★⇒★

renameLookupˢ :
  ∀ {Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) {Σ : Store Ψ} {α : Seal Ψ} {A : Ty 0 Ψ} →
  Σ ∋ˢ α ⦂ A →
  renameStoreˢ ρ Σ ∋ˢ ρ α ⦂ renameˢ ρ A
renameLookupˢ ρ (Z∋ˢ α≡β A≡B) = Z∋ˢ (cong ρ α≡β) (cong (renameˢ ρ) A≡B)
renameLookupˢ ρ (S∋ˢ h) = S∋ˢ (renameLookupˢ ρ h)

liftSubstˢ : ∀{Δ}{Δ′}{Ψ} → Substᵗ Δ Δ′ Ψ → Substᵗ Δ Δ′ (suc Ψ)
liftSubstˢ σ X = ⇑ˢⱽ (σ X)

------------------------------------------------------------------------
-- Private helpers: TVar-level substitution plumbing
------------------------------------------------------------------------
private
  substᵗⱽ :
    ∀{Δ}{Δ′}{Ψ} →
    Substᵗ Δ Δ′ Ψ →
    TVar Δ Ψ →
    TVar Δ′ Ψ
  substᵗⱽ σ (＇ X) = σ X
  substᵗⱽ σ (｀ α) = ｀ α
  
  substᵗ-tvTy :
    ∀{Δ}{Δ′}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (V : TVar Δ Ψ) →
    substᵗ σ (tvTy V) ≡ tvTy (substᵗⱽ σ V)
  substᵗ-tvTy σ (＇ X) = refl
  substᵗ-tvTy σ (｀ α) = refl
  
  infixr 50 _⨟ᵗ_
  _⨟ᵗ_ :
    ∀{Δ}{Δ′}{Δ″}{Ψ} →
    Substᵗ Δ Δ′ Ψ →
    Substᵗ Δ′ Δ″ Ψ →
    Substᵗ Δ Δ″ Ψ
  (σ₁ ⨟ᵗ σ₂) X = substᵗⱽ σ₂ (σ₁ X)
  
  substᵗⱽ-exts-suc :
    ∀{Δ}{Δ′}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (V : TVar Δ Ψ) →
    substᵗⱽ (extsᵗ σ) (renameᵗⱽ Sᵗ V) ≡
    renameᵗⱽ Sᵗ (substᵗⱽ σ V)
  substᵗⱽ-exts-suc σ (＇ X) = refl
  substᵗⱽ-exts-suc σ (｀ α) = refl

------------------------------------------------------------------------
-- Public API: commuting with seal lifting
------------------------------------------------------------------------
renameᵗ-⇑ˢ :
  ∀ {Δ}{Δ′}{Ψ} (ρ : Renameᵗ Δ Δ′) (B : Ty Δ Ψ) →
  renameᵗ ρ (⇑ˢ B) ≡ ⇑ˢ (renameᵗ ρ B)
renameᵗ-⇑ˢ ρ (＇ X) = refl
renameᵗ-⇑ˢ ρ (｀ α) = refl
renameᵗ-⇑ˢ ρ (‵ ι) = refl
renameᵗ-⇑ˢ ρ `★ = refl
renameᵗ-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-⇑ˢ ρ A) (renameᵗ-⇑ˢ ρ B)
renameᵗ-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameᵗ-⇑ˢ (extᵗ ρ) A)

------------------------------------------------------------------------
-- Private helpers: renaming/substitution congruence and composition
------------------------------------------------------------------------
private
  rename-cong :
    ∀{Δ}{Δ′}{Ψ}{ρ ρ′ : Renameᵗ Δ Δ′} →
    ((X : TyVar Δ) → ρ X ≡ ρ′ X) →
    (A : Ty Δ Ψ) →
    renameᵗ ρ A ≡ renameᵗ ρ′ A
  rename-cong h (＇ X) = cong ＇_ (h X)
  rename-cong h (｀ α) = refl
  rename-cong h (‵ ι) = refl
  rename-cong h `★ = refl
  rename-cong h (A ⇒ B) = cong₂ _⇒_ (rename-cong h A) (rename-cong h B)
  rename-cong {ρ = ρ} {ρ′ = ρ′} h (`∀ A) = cong `∀ (rename-cong h-ext A)
    where
      h-ext : (X : TyVar (suc _)) → extᵗ ρ X ≡ extᵗ ρ′ X
      h-ext Zᵗ = refl
      h-ext (Sᵗ X) = cong Sᵗ (h X)
  
  subst-cong :
    ∀{Δ}{Δ′}{Ψ}{σ τ : Substᵗ Δ Δ′ Ψ} →
    ((X : TyVar Δ) → σ X ≡ τ X) →
    (A : Ty Δ Ψ) →
    substᵗ σ A ≡ substᵗ τ A
  subst-cong h (＇ X) = cong tvTy (h X)
  subst-cong h (｀ α) = refl
  subst-cong h (‵ ι) = refl
  subst-cong h `★ = refl
  subst-cong h (A ⇒ B) = cong₂ _⇒_ (subst-cong h A) (subst-cong h B)
  subst-cong {σ = σ} {τ = τ} h (`∀ A) = cong `∀ (subst-cong h-ext A)
    where
      h-ext : (X : TyVar (suc _)) → extsᵗ σ X ≡ extsᵗ τ X
      h-ext Zᵗ = refl
      h-ext (Sᵗ X) = cong (renameᵗⱽ Sᵗ) (h X)
  
  ext-comp :
    ∀{Δ}{Δ′}{Δ″}
    (ρ₁ : Renameᵗ Δ Δ′) (ρ₂ : Renameᵗ Δ′ Δ″) →
    (X : TyVar (suc Δ)) →
    extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X′ → ρ₂ (ρ₁ X′)) X
  ext-comp ρ₁ ρ₂ Zᵗ = refl
  ext-comp ρ₁ ρ₂ (Sᵗ X) = refl
  
  renameᵗⱽ-suc-comm :
    ∀{Δ}{Δ′}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (V : TVar Δ Ψ) →
    renameᵗⱽ (extᵗ ρ) (renameᵗⱽ Sᵗ V) ≡
    renameᵗⱽ Sᵗ (renameᵗⱽ ρ V)
  renameᵗⱽ-suc-comm ρ (＇ X) = refl
  renameᵗⱽ-suc-comm ρ (｀ α) = refl
  
  rename-rename-commute :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (ρ₁ : Renameᵗ Δ Δ′) (ρ₂ : Renameᵗ Δ′ Δ″) (A : Ty Δ Ψ) →
    renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
  rename-rename-commute ρ₁ ρ₂ (＇ X) = refl
  rename-rename-commute ρ₁ ρ₂ (｀ α) = refl
  rename-rename-commute ρ₁ ρ₂ (‵ ι) = refl
  rename-rename-commute ρ₁ ρ₂ `★ = refl
  rename-rename-commute ρ₁ ρ₂ (A ⇒ B) =
    cong₂ _⇒_ (rename-rename-commute ρ₁ ρ₂ A) (rename-rename-commute ρ₁ ρ₂ B)
  rename-rename-commute ρ₁ ρ₂ (`∀ A) =
    trans
      (cong `∀ (rename-rename-commute (extᵗ ρ₁) (extᵗ ρ₂) A))
      (cong `∀ (rename-cong (ext-comp ρ₁ ρ₂) A))
  
  exts-ext-comp :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (τ : Substᵗ Δ′ Δ″ Ψ) (X : TyVar (suc Δ)) →
    extsᵗ τ (extᵗ ρ X) ≡ extsᵗ (λ X′ → τ (ρ X′)) X
  exts-ext-comp ρ τ Zᵗ = refl
  exts-ext-comp ρ τ (Sᵗ X) = refl
  
  renameᵗ-tvTy :
    ∀{Δ}{Δ′}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (V : TVar Δ Ψ) →
    renameᵗ ρ (tvTy V) ≡ tvTy (renameᵗⱽ ρ V)
  renameᵗ-tvTy ρ (＇ X) = refl
  renameᵗ-tvTy ρ (｀ α) = refl
  
  rename-subst-commute :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (τ : Substᵗ Δ′ Δ″ Ψ) (A : Ty Δ Ψ) →
    substᵗ τ (renameᵗ ρ A) ≡ substᵗ (λ X → τ (ρ X)) A
  rename-subst-commute ρ τ (＇ X) = refl
  rename-subst-commute ρ τ (｀ α) = refl
  rename-subst-commute ρ τ (‵ ι) = refl
  rename-subst-commute ρ τ `★ = refl
  rename-subst-commute ρ τ (A ⇒ B) =
    cong₂ _⇒_ (rename-subst-commute ρ τ A) (rename-subst-commute ρ τ B)
  rename-subst-commute ρ τ (`∀ A) =
    trans
      (cong `∀ (rename-subst-commute (extᵗ ρ) (extsᵗ τ) A))
      (cong `∀ (subst-cong (exts-ext-comp ρ τ) A))
  
  ext-exts-comp :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (ρ : Renameᵗ Δ′ Δ″) (τ : Substᵗ Δ Δ′ Ψ) (X : TyVar (suc Δ)) →
    renameᵗⱽ (extᵗ ρ) (extsᵗ τ X) ≡ extsᵗ (λ X′ → renameᵗⱽ ρ (τ X′)) X
  ext-exts-comp ρ τ Zᵗ = refl
  ext-exts-comp ρ τ (Sᵗ X) = renameᵗⱽ-suc-comm ρ (τ X)
  
  rename-subst :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (ρ : Renameᵗ Δ′ Δ″) (τ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
    renameᵗ ρ (substᵗ τ A) ≡ substᵗ (λ X → renameᵗⱽ ρ (τ X)) A
  rename-subst ρ τ (＇ X) = renameᵗ-tvTy ρ (τ X)
  rename-subst ρ τ (｀ α) = refl
  rename-subst ρ τ (‵ ι) = refl
  rename-subst ρ τ `★ = refl
  rename-subst ρ τ (A ⇒ B) =
    cong₂ _⇒_ (rename-subst ρ τ A) (rename-subst ρ τ B)
  rename-subst ρ τ (`∀ A) =
    trans
      (cong `∀ (rename-subst (extᵗ ρ) (extsᵗ τ) A))
      (cong `∀ (subst-cong (ext-exts-comp ρ τ) A))
  
  exts-seq :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (τ : Substᵗ Δ′ Δ″ Ψ) (X : TyVar (suc Δ)) →
    ((extsᵗ σ) ⨟ᵗ (extsᵗ τ)) X ≡ extsᵗ (σ ⨟ᵗ τ) X
  exts-seq σ τ Zᵗ = refl
  exts-seq σ τ (Sᵗ X) = substᵗⱽ-exts-suc τ (σ X)
  
  sub-sub :
    ∀{Δ}{Δ′}{Δ″}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (τ : Substᵗ Δ′ Δ″ Ψ) (A : Ty Δ Ψ) →
    substᵗ τ (substᵗ σ A) ≡ substᵗ (σ ⨟ᵗ τ) A
  sub-sub σ τ (＇ X) = substᵗ-tvTy τ (σ X)
  sub-sub σ τ (｀ α) = refl
  sub-sub σ τ (‵ ι) = refl
  sub-sub σ τ `★ = refl
  sub-sub σ τ (A ⇒ B) =
    cong₂ _⇒_ (sub-sub σ τ A) (sub-sub σ τ B)
  sub-sub σ τ (`∀ A) =
    trans
      (cong `∀ (sub-sub (extsᵗ σ) (extsᵗ τ) A))
      (cong `∀ (subst-cong (exts-seq σ τ) A))
  
  cons-sub :
    ∀{Δ}{Δ′}{Ψ} →
    TVar Δ′ Ψ →
    Substᵗ Δ Δ′ Ψ →
    Substᵗ (suc Δ) Δ′ Ψ
  cons-sub v σ Zᵗ = v
  cons-sub v σ (Sᵗ X) = σ X
  
  singleTyEnv-suc-cancelⱽ :
    ∀{Δ}{Ψ}
    (v : TVar Δ Ψ) (V : TVar Δ Ψ) →
    substᵗⱽ (singleTyEnv v) (renameᵗⱽ Sᵗ V) ≡ V
  singleTyEnv-suc-cancelⱽ v (＇ X) = refl
  singleTyEnv-suc-cancelⱽ v (｀ α) = refl
  
  exts-sub-cons :
    ∀{Δ}{Δ′}{Ψ}
    {σ : Substᵗ Δ Δ′ Ψ} {A : Ty (suc Δ) Ψ} {v : TVar Δ′ Ψ} →
    (substᵗ (extsᵗ σ) A) [ v ]ᵗ ≡ substᵗ (cons-sub v σ) A
  exts-sub-cons {σ = σ} {A = A} {v = v} =
    trans
      (sub-sub (extsᵗ σ) (singleTyEnv v) A)
      (subst-cong env-eq A)
    where
      env-eq :
        (X : TyVar (suc _)) →
        ((extsᵗ σ) ⨟ᵗ (singleTyEnv v)) X ≡ cons-sub v σ X
      env-eq Zᵗ = refl
      env-eq (Sᵗ X) = singleTyEnv-suc-cancelⱽ v (σ X)
  
  subst-[]ᵗ-commute :
    ∀{Δ}{Δ′}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) (B : TVar Δ Ψ) →
    substᵗ σ (A [ B ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ substᵗⱽ σ B ]ᵗ
  subst-[]ᵗ-commute σ A B =
    trans
      (sub-sub (singleTyEnv B) σ A)
      (trans
        (subst-cong env-eq A)
        (sym (exts-sub-cons {σ = σ} {A = A} {v = substᵗⱽ σ B})))
    where
      env-eq :
        (X : TyVar (suc _)) →
        ((singleTyEnv B) ⨟ᵗ σ) X ≡ cons-sub (substᵗⱽ σ B) σ X
      env-eq Zᵗ = refl
      env-eq (Sᵗ X) = refl
  
  renSubst :
    ∀{Δ}{Δ′}{Ψ} →
    Renameᵗ Δ Δ′ →
    Substᵗ Δ Δ′ Ψ
  renSubst ρ X = ＇ (ρ X)
  
  exts-renSubst :
    ∀{Δ}{Δ′}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (X : TyVar (suc Δ)) →
    extsᵗ (renSubst {Ψ = Ψ} ρ) X ≡ renSubst {Ψ = Ψ} (extᵗ ρ) X
  exts-renSubst ρ Zᵗ = refl
  exts-renSubst ρ (Sᵗ X) = refl
  
  substᵗ-renSubst :
    ∀{Δ}{Δ′}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (A : Ty Δ Ψ) →
    substᵗ (renSubst ρ) A ≡ renameᵗ ρ A
  substᵗ-renSubst ρ (＇ X) = refl
  substᵗ-renSubst ρ (｀ α) = refl
  substᵗ-renSubst ρ (‵ ι) = refl
  substᵗ-renSubst ρ `★ = refl
  substᵗ-renSubst ρ (A ⇒ B) =
    cong₂ _⇒_ (substᵗ-renSubst ρ A) (substᵗ-renSubst ρ B)
  substᵗ-renSubst {Ψ = Ψ} ρ (`∀ A) =
    cong `∀
      (trans
        (subst-cong (exts-renSubst {Ψ = Ψ} ρ) A)
        (substᵗ-renSubst (extᵗ ρ) A))
  
  renameᵗ-renameˢ :
    ∀{Δ}{Δ′}{Ψ}{Ψ′}
    (ρ : Renameᵗ Δ Δ′) (ϱ : Renameˢ Ψ Ψ′) (A : Ty Δ Ψ) →
    renameᵗ ρ (renameˢ ϱ A) ≡ renameˢ ϱ (renameᵗ ρ A)
  renameᵗ-renameˢ ρ ϱ (＇ X) = refl
  renameᵗ-renameˢ ρ ϱ (｀ α) = refl
  renameᵗ-renameˢ ρ ϱ (‵ ι) = refl
  renameᵗ-renameˢ ρ ϱ `★ = refl
  renameᵗ-renameˢ ρ ϱ (A ⇒ B) =
    cong₂ _⇒_
      (renameᵗ-renameˢ ρ ϱ A)
      (renameᵗ-renameˢ ρ ϱ B)
  renameᵗ-renameˢ ρ ϱ (`∀ A) =
    cong `∀ (renameᵗ-renameˢ (extᵗ ρ) ϱ A)
  
  rename-[]ᵗ-commute :
    ∀{Δ}{Δ′}{Ψ}
    (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) (B : TVar Δ Ψ) →
    renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗⱽ ρ B ]ᵗ
  rename-[]ᵗ-commute ρ A B =
    trans
      (rename-subst ρ (singleTyEnv B) A)
      (trans
        (subst-cong env-eq A)
        (sym (rename-subst-commute (extᵗ ρ) (singleTyEnv (renameᵗⱽ ρ B)) A)))
    where
      env-eq :
        (X : TyVar (suc _)) →
        (λ X′ → renameᵗⱽ ρ (singleTyEnv B X′)) X ≡
        (λ X′ → singleTyEnv (renameᵗⱽ ρ B) (extᵗ ρ X′)) X
      env-eq Zᵗ = refl
      env-eq (Sᵗ X) = refl
  
------------------------------------------------------------------------
-- Public API: type-renaming source lemma for ν
------------------------------------------------------------------------
renameᵗ-ν-src :
  ∀ {Δ}{Δ′}{Ψ} (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) →
  renameᵗ ρ (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (renameᵗ (extᵗ ρ) A)) [ ｀ Zˢ ]ᵗ)
renameᵗ-ν-src ρ A =
  trans
    (rename-[]ᵗ-commute ρ (⇑ˢ A) (｀ Zˢ))
    (cong (λ C → C [ ｀ Zˢ ]ᵗ) (renameᵗ-⇑ˢ (extᵗ ρ) A))

------------------------------------------------------------------------
-- Private helpers: seal-renaming interaction with TVar substitution
------------------------------------------------------------------------
private
  renameˢ-tvTy :
    ∀{Δ}{Ψ}{Ψ′}
    (ρ : Renameˢ Ψ Ψ′) (V : TVar Δ Ψ) →
    renameˢ ρ (tvTy V) ≡ tvTy (renameˢⱽ ρ V)
  renameˢ-tvTy ρ (＇ X) = refl
  renameˢ-tvTy ρ (｀ α) = refl
  
  renameᵗⱽ-renameˢⱽ :
    ∀{Δ}{Δ′}{Ψ}{Ψ′}
    (ρ : Renameᵗ Δ Δ′) (ϱ : Renameˢ Ψ Ψ′) (V : TVar Δ Ψ) →
    renameᵗⱽ ρ (renameˢⱽ ϱ V) ≡ renameˢⱽ ϱ (renameᵗⱽ ρ V)
  renameᵗⱽ-renameˢⱽ ρ ϱ (＇ X) = refl
  renameᵗⱽ-renameˢⱽ ρ ϱ (｀ α) = refl
  
  exts-liftSubstˢ :
    ∀{Δ}{Δ′}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (X : TyVar (suc Δ)) →
    extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
  exts-liftSubstˢ σ Zᵗ = refl
  exts-liftSubstˢ σ (Sᵗ X) =
    renameᵗⱽ-renameˢⱽ Sᵗ Sˢ (σ X)

------------------------------------------------------------------------
-- Public API: type-substitution commuting with seal lifting
------------------------------------------------------------------------
substᵗ-⇑ˢ :
  ∀ {Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (B : Ty Δ Ψ) →
  substᵗ (liftSubstˢ σ) (⇑ˢ B) ≡ ⇑ˢ (substᵗ σ B)
substᵗ-⇑ˢ σ (＇ X) = sym (renameˢ-tvTy Sˢ (σ X))
substᵗ-⇑ˢ σ (｀ α) = refl
substᵗ-⇑ˢ σ (‵ ι) = refl
substᵗ-⇑ˢ σ `★ = refl
substᵗ-⇑ˢ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-⇑ˢ σ A) (substᵗ-⇑ˢ σ B)
substᵗ-⇑ˢ σ (`∀ A) =
  cong `∀
    (trans
      (subst-cong (exts-liftSubstˢ σ) (⇑ˢ A))
      (substᵗ-⇑ˢ (extsᵗ σ) A))

renameᵗ-wkTy0 :
  ∀ {Δ}{Δ′}{Ψ} (ρ : Renameᵗ Δ Δ′) (A : Ty 0 Ψ) →
  renameᵗ ρ (wkTy0 A) ≡ wkTy0 A
renameᵗ-wkTy0 ρ A =
  trans
    (rename-rename-commute lift0ᵗ ρ A)
    (rename-cong env-eq A)
  where
    env-eq :
      (X : TyVar 0) →
      (λ X′ → ρ (lift0ᵗ X′)) X ≡ lift0ᵗ X
    env-eq ()

substᵗ-wkTy0 :
  ∀ {Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (A : Ty 0 Ψ) →
  substᵗ σ (wkTy0 A) ≡ wkTy0 A
substᵗ-wkTy0 σ A =
  trans
    (rename-subst-commute lift0ᵗ σ A)
    (trans
      (subst-cong env-eq A)
      (substᵗ-renSubst lift0ᵗ A))
  where
    env-eq :
      (X : TyVar 0) →
      (λ X′ → σ (lift0ᵗ X′)) X ≡ renSubst lift0ᵗ X
    env-eq ()

renameˢ-⇑ˢ :
  ∀ {Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (B : Ty Δ Ψ) →
  renameˢ (extˢ ρ) (⇑ˢ B) ≡ ⇑ˢ (renameˢ ρ B)
renameˢ-⇑ˢ ρ (＇ X) = refl
renameˢ-⇑ˢ ρ (｀ α) = refl
renameˢ-⇑ˢ ρ (‵ ι) = refl
renameˢ-⇑ˢ ρ `★ = refl
renameˢ-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-⇑ˢ ρ A) (renameˢ-⇑ˢ ρ B)
renameˢ-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameˢ-⇑ˢ ρ A)

------------------------------------------------------------------------
-- Private helpers: seal-renaming/substitution commuting
------------------------------------------------------------------------
private
  renameˢ-substᵗ-commute :
    ∀{Δ}{Δ′}{Ψ}{Ψ′}
    (ρ : Renameˢ Ψ Ψ′) (σ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
    renameˢ ρ (substᵗ σ A) ≡
    substᵗ (λ X → renameˢⱽ ρ (σ X)) (renameˢ ρ A)
  renameˢ-substᵗ-commute ρ σ (＇ X) = renameˢ-tvTy ρ (σ X)
  renameˢ-substᵗ-commute ρ σ (｀ α) = refl
  renameˢ-substᵗ-commute ρ σ (‵ ι) = refl
  renameˢ-substᵗ-commute ρ σ `★ = refl
  renameˢ-substᵗ-commute ρ σ (A ⇒ B) =
    cong₂ _⇒_
      (renameˢ-substᵗ-commute ρ σ A)
      (renameˢ-substᵗ-commute ρ σ B)
  renameˢ-substᵗ-commute ρ σ (`∀ A) =
    cong `∀
      (trans
        (renameˢ-substᵗ-commute ρ (extsᵗ σ) A)
        (subst-cong env-eq (renameˢ ρ A)))
    where
      env-eq :
        (X : TyVar (suc _)) →
        renameˢⱽ ρ (extsᵗ σ X) ≡ extsᵗ (λ X′ → renameˢⱽ ρ (σ X′)) X
      env-eq Zᵗ = refl
      env-eq (Sᵗ X) = sym (renameᵗⱽ-renameˢⱽ Sᵗ ρ (σ X))
  
  renameˢ-[]ᵗ-commute :
    ∀{Δ}{Ψ}{Ψ′}
    (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) (B : TVar Δ Ψ) →
    renameˢ ρ (A [ B ]ᵗ) ≡ (renameˢ ρ A) [ renameˢⱽ ρ B ]ᵗ
  renameˢ-[]ᵗ-commute ρ A B =
    trans
      (renameˢ-substᵗ-commute ρ (singleTyEnv B) A)
      (subst-cong env-eq (renameˢ ρ A))
    where
      env-eq :
        (X : TyVar (suc _)) →
        (λ X′ → renameˢⱽ ρ (singleTyEnv B X′)) X ≡
        singleTyEnv (renameˢⱽ ρ B) X
      env-eq Zᵗ = refl
      env-eq (Sᵗ X) = refl

------------------------------------------------------------------------
-- Public API: seal-renaming source and weakening lemmas
------------------------------------------------------------------------
renameˢ-ν-src :
  ∀ {Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) →
  renameˢ (extˢ ρ) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (renameˢ ρ A)) [ ｀ Zˢ ]ᵗ)
renameˢ-ν-src ρ A =
  trans
    (renameˢ-[]ᵗ-commute (extˢ ρ) (⇑ˢ A) (｀ Zˢ))
    (cong (λ C → C [ ｀ Zˢ ]ᵗ) (renameˢ-⇑ˢ ρ A))

renameˢ-wkTy0 :
  ∀ {Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (A : Ty 0 Ψ) →
  renameˢ ρ (wkTy0 {Δ = Δ} A) ≡ wkTy0 (renameˢ ρ A)
renameˢ-wkTy0 ρ A = sym (renameᵗ-renameˢ lift0ᵗ ρ A)

------------------------------------------------------------------------
-- Private helpers: store lifting under seal renaming
------------------------------------------------------------------------
private
  renameStoreˢ-suc :
    ∀ {Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (Σ : Store Ψ) →
    renameStoreˢ (extˢ ρ) (⟰ˢ Σ) ≡ ⟰ˢ (renameStoreˢ ρ Σ)
  renameStoreˢ-suc ρ [] = refl
  renameStoreˢ-suc ρ ((α , A) ∷ Σ) =
    cong₂ _∷_
      (cong₂ _,_ refl (renameˢ-⇑ˢ ρ A))
      (renameStoreˢ-suc ρ Σ)

------------------------------------------------------------------------
-- Public API: store source shape and ν substitution source
------------------------------------------------------------------------
renameStoreˢ-↑★ :
  ∀ {Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (Σ : Store Ψ) →
  renameStoreˢ (extˢ ρ) ((Zˢ , `★) ∷ ⟰ˢ Σ) ≡
  (Zˢ , `★) ∷ ⟰ˢ (renameStoreˢ ρ Σ)
renameStoreˢ-↑★ ρ Σ =
  cong ((Zˢ , `★) ∷_) (renameStoreˢ-suc ρ Σ)

substᵗ-ν-src :
  ∀ {Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) →
  substᵗ (liftSubstˢ σ) (((⇑ˢ A) [ ｀ Zˢ ]ᵗ)) ≡
  ((⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ Zˢ ]ᵗ)
substᵗ-ν-src σ A =
  trans
    (subst-[]ᵗ-commute (liftSubstˢ σ) (⇑ˢ A) (｀ Zˢ))
    (cong
      (λ C → C [ ｀ Zˢ ]ᵗ)
      (trans
        (subst-cong (exts-liftSubstˢ σ) (⇑ˢ A))
        (substᵗ-⇑ˢ (extsᵗ σ) A)))
