module TypeSubst where

-- File Charter:
--   * Generic metatheory for type-level renaming/substitution on `Ty`.
--   * Substitution algebra laws, commutation lemmas, and instantiation lemmas.
--   * No context-shape lemmas (put those in `Ctx`) and no coercion-specific lemmas.
-- Note to self:
--   * Before adding a theorem here, check whether it is really about `Ty` substitution
--     itself; if it mentions context lookup/store/coercions as primary structure,
--     place it in that module instead.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types

------------------------------------------------------------------------
-- Public API: basic lemmas
------------------------------------------------------------------------

renameᵗ-ground : ∀{Δ Δ′}{Ψ}{G : Ty Δ Ψ} (ρ : Renameᵗ Δ Δ′)
  → Ground G
  → Ground (renameᵗ ρ G)
renameᵗ-ground ρ (｀ α) = ｀ α
renameᵗ-ground ρ (‵ ι) = ‵ ι
renameᵗ-ground ρ ★⇒★ = ★⇒★

substᵗ-ground : ∀{Δ Δ′}{Ψ}{G : Ty Δ Ψ} (σ : Substᵗ Δ Δ′ Ψ)
  → Ground G
  → Ground (substᵗ σ G)
substᵗ-ground σ (｀ α) = ｀ α
substᵗ-ground σ (‵ ι) = ‵ ι
substᵗ-ground σ ★⇒★ = ★⇒★

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
renameLookupˢ ρ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ (cong ρ α≡β) (cong (renameˢ ρ) A≡B)
renameLookupˢ ρ (S∋ˢ h) = S∋ˢ (renameLookupˢ ρ h)

liftSubstˢ : ∀{Δ}{Δ′}{Ψ} → Substᵗ Δ Δ′ Ψ → Substᵗ Δ Δ′ (suc Ψ)
liftSubstˢ σ X = ⇑ˢ (σ X)

------------------------------------------------------------------------
-- Core renaming/substitution infrastructure
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

substᵗ-cong :
  ∀{Δ}{Δ′}{Ψ}
  {σ τ : Substᵗ Δ Δ′ Ψ} →
  ((X : TyVar Δ) → σ X ≡ τ X) →
  (A : Ty Δ Ψ) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (＇ X) = h X
substᵗ-cong h (｀ α) = refl
substᵗ-cong h (‵ ι) = refl
substᵗ-cong h `★ = refl
substᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ = σ} {τ = τ} h (`∀ A) =
  cong `∀ (substᵗ-cong h-ext A)
  where
    h-ext : (X : TyVar (suc _)) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext Zᵗ = refl
    h-ext (Sᵗ X) = cong (renameᵗ Sᵗ) (h X)

substᵗ-id :
  ∀{Δ}{Ψ} (A : Ty Δ Ψ) →
  substᵗ (λ X → ＇ X) A ≡ A
substᵗ-id (＇ X) = refl
substᵗ-id (｀ α) = refl
substᵗ-id (‵ ι) = refl
substᵗ-id `★ = refl
substᵗ-id (A ⇒ B) = cong₂ _⇒_ (substᵗ-id A) (substᵗ-id B)
substᵗ-id (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong env-eq A)
      (substᵗ-id A))
  where
    env-eq : (X : TyVar (suc _)) → extsᵗ (λ Y → ＇ Y) X ≡ ＇ X
    env-eq Zᵗ = refl
    env-eq (Sᵗ X) = refl

renameᵗ-compose :
  ∀{Δ}{Δ′}{Δ″}{Ψ}
  (ρ₁ : Renameᵗ Δ Δ′) (ρ₂ : Renameᵗ Δ′ Δ″) (A : Ty Δ Ψ) →
  renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
renameᵗ-compose ρ₁ ρ₂ (＇ X) = refl
renameᵗ-compose ρ₁ ρ₂ (｀ α) = refl
renameᵗ-compose ρ₁ ρ₂ (‵ ι) = refl
renameᵗ-compose ρ₁ ρ₂ `★ = refl
renameᵗ-compose ρ₁ ρ₂ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-compose ρ₁ ρ₂ A) (renameᵗ-compose ρ₁ ρ₂ B)
renameᵗ-compose ρ₁ ρ₂ (`∀ A) =
  trans
    (cong `∀ (renameᵗ-compose (extᵗ ρ₁) (extᵗ ρ₂) A))
    (cong `∀ (rename-cong ext-comp A))
  where
    ext-comp :
      (X : TyVar (suc _)) →
      extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X′ → ρ₂ (ρ₁ X′)) X
    ext-comp Zᵗ = refl
    ext-comp (Sᵗ X) = refl

renameᵗ-suc-comm :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty Δ Ψ) →
  renameᵗ Sᵗ (renameᵗ ρ A) ≡
  renameᵗ (extᵗ ρ) (renameᵗ Sᵗ A)
renameᵗ-suc-comm ρ A =
  trans
    (renameᵗ-compose ρ Sᵗ A)
    (sym (renameᵗ-compose Sᵗ (extᵗ ρ) A))

substᵗ-renameᵗ :
  ∀{Δ}{Δ′}{Δ″}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (σ : Substᵗ Δ′ Δ″ Ψ) (A : Ty Δ Ψ) →
  substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-renameᵗ ρ σ (＇ X) = refl
substᵗ-renameᵗ ρ σ (｀ α) = refl
substᵗ-renameᵗ ρ σ (‵ ι) = refl
substᵗ-renameᵗ ρ σ `★ = refl
substᵗ-renameᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renameᵗ ρ σ A) (substᵗ-renameᵗ ρ σ B)
substᵗ-renameᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-renameᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar (suc _)) →
      extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
    env-eq Zᵗ = refl
    env-eq (Sᵗ X) = refl

renameᵗ-substᵗ :
  ∀{Δ}{Δ′}{Δ″}{Ψ}
  (ρ : Renameᵗ Δ′ Δ″) (σ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
  renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
renameᵗ-substᵗ ρ σ (＇ X) = refl
renameᵗ-substᵗ ρ σ (｀ α) = refl
renameᵗ-substᵗ ρ σ (‵ ι) = refl
renameᵗ-substᵗ ρ σ `★ = refl
renameᵗ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-substᵗ ρ σ A) (renameᵗ-substᵗ ρ σ B)
renameᵗ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameᵗ-substᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar (suc _)) →
      renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡ extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
    env-eq Zᵗ = refl
    env-eq (Sᵗ X) = sym (renameᵗ-suc-comm ρ (σ X))

substᵗ-suc-renameᵗ-suc :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
  substᵗ (extsᵗ σ) (renameᵗ Sᵗ A) ≡
  renameᵗ Sᵗ (substᵗ σ A)
substᵗ-suc-renameᵗ-suc σ A =
  trans
    (substᵗ-renameᵗ Sᵗ (extsᵗ σ) A)
    (sym (renameᵗ-substᵗ Sᵗ σ A))

substᵗ-substᵗ :
  ∀{Δ}{Δ′}{Δ″}{Ψ}
  (σ : Substᵗ Δ′ Δ″ Ψ) (τ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
  substᵗ σ (substᵗ τ A) ≡
  substᵗ (λ X → substᵗ σ (τ X)) A
substᵗ-substᵗ σ τ (＇ X) = refl
substᵗ-substᵗ σ τ (｀ α) = refl
substᵗ-substᵗ σ τ (‵ ι) = refl
substᵗ-substᵗ σ τ `★ = refl
substᵗ-substᵗ σ τ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-substᵗ σ τ A) (substᵗ-substᵗ σ τ B)
substᵗ-substᵗ σ τ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-substᵗ (extsᵗ σ) (extsᵗ τ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar (suc _)) →
      substᵗ (extsᵗ σ) (extsᵗ τ X) ≡
      extsᵗ (λ Y → substᵗ σ (τ Y)) X
    env-eq Zᵗ = refl
    env-eq (Sᵗ X) = substᵗ-suc-renameᵗ-suc σ (τ X)

------------------------------------------------------------------------
-- Seal renaming commutation
------------------------------------------------------------------------

renameˢ-renameᵗ :
  ∀{Δ}{Δ′}{Ψ}{Ψ′}
  (ρᵗ : Renameᵗ Δ Δ′) (ρˢ : Renameˢ Ψ Ψ′) (A : Ty Δ Ψ) →
  renameˢ ρˢ (renameᵗ ρᵗ A) ≡
  renameᵗ ρᵗ (renameˢ ρˢ A)
renameˢ-renameᵗ ρᵗ ρˢ (＇ X) = refl
renameˢ-renameᵗ ρᵗ ρˢ (｀ α) = refl
renameˢ-renameᵗ ρᵗ ρˢ (‵ ι) = refl
renameˢ-renameᵗ ρᵗ ρˢ `★ = refl
renameˢ-renameᵗ ρᵗ ρˢ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-renameᵗ ρᵗ ρˢ A) (renameˢ-renameᵗ ρᵗ ρˢ B)
renameˢ-renameᵗ ρᵗ ρˢ (`∀ A) =
  cong `∀ (renameˢ-renameᵗ (extᵗ ρᵗ) ρˢ A)

renameᵗ-renameˢ :
  ∀{Δ}{Δ′}{Ψ}{Ψ′}
  (ρ : Renameᵗ Δ Δ′) (ϱ : Renameˢ Ψ Ψ′) (A : Ty Δ Ψ) →
  renameᵗ ρ (renameˢ ϱ A) ≡ renameˢ ϱ (renameᵗ ρ A)
renameᵗ-renameˢ ρ ϱ (＇ X) = refl
renameᵗ-renameˢ ρ ϱ (｀ α) = refl
renameᵗ-renameˢ ρ ϱ (‵ ι) = refl
renameᵗ-renameˢ ρ ϱ `★ = refl
renameᵗ-renameˢ ρ ϱ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-renameˢ ρ ϱ A) (renameᵗ-renameˢ ρ ϱ B)
renameᵗ-renameˢ ρ ϱ (`∀ A) =
  cong `∀ (renameᵗ-renameˢ (extᵗ ρ) ϱ A)

renameˢ-substᵗ :
  ∀{Δ}{Δ′}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (σ : Substᵗ Δ Δ′ Ψ) (A : Ty Δ Ψ) →
  renameˢ ρ (substᵗ σ A) ≡
  substᵗ (λ X → renameˢ ρ (σ X)) (renameˢ ρ A)
renameˢ-substᵗ ρ σ (＇ X) = refl
renameˢ-substᵗ ρ σ (｀ α) = refl
renameˢ-substᵗ ρ σ (‵ ι) = refl
renameˢ-substᵗ ρ σ `★ = refl
renameˢ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-substᵗ ρ σ A) (renameˢ-substᵗ ρ σ B)
renameˢ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameˢ-substᵗ ρ (extsᵗ σ) A)
      (substᵗ-cong env-eq (renameˢ ρ A)))
  where
    env-eq :
      (X : TyVar (suc _)) →
      renameˢ ρ (extsᵗ σ X) ≡ extsᵗ (λ Y → renameˢ ρ (σ Y)) X
    env-eq Zᵗ = refl
    env-eq (Sᵗ X) = sym (renameᵗ-renameˢ Sᵗ ρ (σ X))

inst★-renameᵗ-suc :
  ∀{Δ}{Ψ} (A : Ty Δ Ψ) →
  (renameᵗ Sᵗ A) [ `★ ]ᵗ ≡ A
inst★-renameᵗ-suc A =
  trans
    (substᵗ-renameᵗ Sᵗ (singleTyEnv `★) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-inst★ :
  ∀{Δ}{Δ′}{Ψ}
  (ρ : Renameᵗ Δ Δ′) (A : Ty (suc Δ) Ψ) →
  renameᵗ ρ (A [ `★ ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ `★ ]ᵗ
renameᵗ-inst★ {Ψ = Ψ} ρ A =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv `★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv `★) A)))
  where
    env :
      (X : TyVar (suc _)) →
      renameᵗ ρ (singleTyEnv (`★ {Ψ = Ψ}) X) ≡
      singleTyEnv (`★ {Ψ = Ψ}) (extᵗ ρ X)
    env Zᵗ = refl
    env (Sᵗ X) = refl

substᵗ-inst★ :
  ∀{Δ}{Δ′}{Ψ}
  (σ : Substᵗ Δ Δ′ Ψ) (A : Ty (suc Δ) Ψ) →
  substᵗ σ (A [ `★ ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ `★ ]ᵗ
substᵗ-inst★ σ A =
  trans
    (substᵗ-substᵗ σ (singleTyEnv `★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv `★) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar (suc _)) →
      substᵗ σ (singleTyEnv `★ X) ≡ substᵗ (singleTyEnv `★) (extsᵗ σ X)
    env Zᵗ = refl
    env (Sᵗ X) = sym (inst★-renameᵗ-suc (σ X))

renameˢ-inst★ :
  ∀{Δ}{Ψ}{Ψ′}
  (ρ : Renameˢ Ψ Ψ′) (A : Ty (suc Δ) Ψ) →
  renameˢ ρ (A [ `★ ]ᵗ) ≡ (renameˢ ρ A) [ `★ ]ᵗ
renameˢ-inst★ ρ A =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv `★) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar (suc _)) →
      renameˢ ρ (singleTyEnv `★ X) ≡ singleTyEnv `★ X
    env Zᵗ = refl
    env (Sᵗ X) = refl

------------------------------------------------------------------------
-- Commuting with seal lifting/opening and contexts
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

private
  exts-liftSubstˢ :
    ∀{Δ}{Δ′}{Ψ}
    (σ : Substᵗ Δ Δ′ Ψ) (X : TyVar (suc Δ)) →
    extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
  exts-liftSubstˢ σ Zᵗ = refl
  exts-liftSubstˢ σ (Sᵗ X) = renameᵗ-⇑ˢ Sᵗ (σ X)

substᵗ-⇑ˢ :
  ∀ {Δ}{Δ′}{Ψ} (σ : Substᵗ Δ Δ′ Ψ) (B : Ty Δ Ψ) →
  substᵗ (liftSubstˢ σ) (⇑ˢ B) ≡ ⇑ˢ (substᵗ σ B)
substᵗ-⇑ˢ σ (＇ X) = refl
substᵗ-⇑ˢ σ (｀ α) = refl
substᵗ-⇑ˢ σ (‵ ι) = refl
substᵗ-⇑ˢ σ `★ = refl
substᵗ-⇑ˢ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-⇑ˢ σ A) (substᵗ-⇑ˢ σ B)
substᵗ-⇑ˢ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
      (substᵗ-⇑ˢ (extsᵗ σ) A))

------------------------------------------------------------------------
-- Closed-type weakening invariants
------------------------------------------------------------------------

private
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
        (substᵗ-cong (exts-renSubst {Ψ = Ψ} ρ) A)
        (substᵗ-renSubst (extᵗ ρ) A))

renameᵗ-wkTy0 :
  ∀ {Δ}{Δ′}{Ψ} (ρ : Renameᵗ Δ Δ′) (A : Ty 0 Ψ) →
  renameᵗ ρ (wkTy0 A) ≡ wkTy0 A
renameᵗ-wkTy0 ρ A =
  trans
    (renameᵗ-compose lift0ᵗ ρ A)
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
    (substᵗ-renameᵗ lift0ᵗ σ A)
    (trans
      (substᵗ-cong env-eq A)
      (substᵗ-renSubst lift0ᵗ A))
  where
    env-eq :
      (X : TyVar 0) →
      (λ X′ → σ (lift0ᵗ X′)) X ≡ renSubst lift0ᵗ X
    env-eq ()

renameˢ-wkTy0 :
  ∀ {Δ}{Ψ}{Ψ′} (ρ : Renameˢ Ψ Ψ′) (A : Ty 0 Ψ) →
  renameˢ ρ (wkTy0 {Δ = Δ} A) ≡ wkTy0 {Δ = Δ} (renameˢ ρ A)
renameˢ-wkTy0 ρ A = sym (renameᵗ-renameˢ lift0ᵗ ρ A)

------------------------------------------------------------------------
-- Useful seal-opening identity (used by Store.agda)
------------------------------------------------------------------------

renameˢ-single-⇑ˢ-id :
  ∀{Δ}{Ψ} →
  (α : Seal Ψ) →
  (A : Ty Δ Ψ) →
  renameˢ (singleSealEnv α) (⇑ˢ A) ≡ A
renameˢ-single-⇑ˢ-id α (＇ X) = refl
renameˢ-single-⇑ˢ-id α (｀ β) = refl
renameˢ-single-⇑ˢ-id α (‵ ι) = refl
renameˢ-single-⇑ˢ-id α `★ = refl
renameˢ-single-⇑ˢ-id α (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-single-⇑ˢ-id α A) (renameˢ-single-⇑ˢ-id α B)
renameˢ-single-⇑ˢ-id α (`∀ A) =
  cong `∀ (renameˢ-single-⇑ˢ-id α A)
