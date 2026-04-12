module TypeProperties where

-- File Charter:
--   * Generic metatheory for type-level operations on `Ty` such as renaming/substitution.
--   * Substitution algebra laws, commutation lemmas, and instantiation lemmas.
--   * No context-shape lemmas (put those in `Ctx`) and no coercion-specific lemmas.
-- Note to self:
--   * Before adding a theorem here, check whether it is really about `Ty` itself;
--     if it mentions context lookup/store/coercions as primary structure,
--     place it in that module instead.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (zero; suc; _<_; z<s; s<s)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import Types

------------------------------------------------------------------------
-- Public API: basic lemmas
------------------------------------------------------------------------

renameᵗ-ground : ∀{G : Ty} (ρ : Renameᵗ)
  → Ground G
  → Ground (renameᵗ ρ G)
renameᵗ-ground ρ (｀ α) = ｀ α
renameᵗ-ground ρ (‵ ι) = ‵ ι
renameᵗ-ground ρ ★⇒★ = ★⇒★

substᵗ-ground : ∀{G : Ty} (σ : Substᵗ)
  → Ground G
  → Ground (substᵗ σ G)
substᵗ-ground σ (｀ α) = ｀ α
substᵗ-ground σ (‵ ι) = ‵ ι
substᵗ-ground σ ★⇒★ = ★⇒★

renameˢ-ground : ∀{G : Ty} (ρ : Renameˢ)
  → Ground G
  → Ground (renameˢ ρ G)
renameˢ-ground ρ (｀ α) = ｀ (ρ α)
renameˢ-ground ρ (‵ ι) = ‵ ι
renameˢ-ground ρ ★⇒★ = ★⇒★

renameLookupˢ :
  ∀  (ρ : Renameˢ) {Σ : Store} {α : Seal} {A : Ty} →
  Σ ∋ˢ α ⦂ A →
  renameStoreˢ ρ Σ ∋ˢ ρ α ⦂ renameˢ ρ A
renameLookupˢ ρ (Z∋ˢ α≡β A≡B) =
  Z∋ˢ (cong ρ α≡β) (cong (renameˢ ρ) A≡B)
renameLookupˢ ρ (S∋ˢ h) = S∋ˢ (renameLookupˢ ρ h)

liftSubstˢ :  Substᵗ → Substᵗ
liftSubstˢ σ X = ⇑ˢ (σ X)

------------------------------------------------------------------------
-- Well-formedness preserved by renaming and substitution
------------------------------------------------------------------------

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ′ ρ = ∀ {X} → X < Δ → ρ X < Δ′

TyRenameWf-ext :
  ∀ {Δ Δ′} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ′ ρ →
  TyRenameWf (suc Δ) (suc Δ′) (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s X<Δ) = s<s (hρ X<Δ)

TyRenameWf-suc :
  ∀ {Δ} →
  TyRenameWf Δ (suc Δ) suc
TyRenameWf-suc {Δ} X<Δ = s<s X<Δ

SealRenameWf : SealCtx → SealCtx → Renameˢ → Set
SealRenameWf Ψ Ψ′ ρ = ∀ {α} → α < Ψ → ρ α < Ψ′

SealRenameWf-ext :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  SealRenameWf (suc Ψ) (suc Ψ′) (extˢ ρ)
SealRenameWf-ext hρ {zero} z<s = z<s
SealRenameWf-ext hρ {suc α} (s<s α<Ψ) = s<s (hρ α<Ψ)

SealRenameWf-suc :
  ∀ {Ψ} →
  SealRenameWf Ψ (suc Ψ) suc
SealRenameWf-suc α<Ψ = s<s α<Ψ

renameᵗ-preserves-WfTy :
  ∀ {Δ Δ′ Ψ} {ρ : Renameᵗ} {A : Ty} →
  WfTy Δ Ψ A →
  TyRenameWf Δ Δ′ ρ →
  WfTy Δ′ Ψ (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfVar X<Δ) hρ = wfVar (hρ X<Δ)
renameᵗ-preserves-WfTy (wfSeal α<Ψ) hρ = wfSeal α<Ψ
renameᵗ-preserves-WfTy wfBase hρ = wfBase
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy (wf∀ hA) hρ =
  wf∀ (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ))

renameˢ-preserves-WfTy :
  ∀ {Δ Ψ Ψ′} {ρ : Renameˢ} {A : Ty} →
  WfTy Δ Ψ A →
  SealRenameWf Ψ Ψ′ ρ →
  WfTy Δ Ψ′ (renameˢ ρ A)
renameˢ-preserves-WfTy (wfVar X<Δ) hρ = wfVar X<Δ
renameˢ-preserves-WfTy (wfSeal α<Ψ) hρ = wfSeal (hρ α<Ψ)
renameˢ-preserves-WfTy wfBase hρ = wfBase
renameˢ-preserves-WfTy wf★ hρ = wf★
renameˢ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameˢ-preserves-WfTy hA hρ) (renameˢ-preserves-WfTy hB hρ)
renameˢ-preserves-WfTy (wf∀ hA) hρ =
  wf∀ (renameˢ-preserves-WfTy hA hρ)

TySubstWf : TyCtx → TyCtx → SealCtx → Substᵗ → Set
TySubstWf Δ Δ′ Ψ σ = ∀ {X} → X < Δ → WfTy Δ′ Ψ (σ X)

TySubstWf-exts :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} →
  TySubstWf Δ Δ′ Ψ σ →
  TySubstWf (suc Δ) (suc Δ′) Ψ (extsᵗ σ)
TySubstWf-exts hσ {zero} z<s = wfVar z<s
TySubstWf-exts hσ {suc X} (s<s X<Δ) =
  renameᵗ-preserves-WfTy (hσ X<Δ) TyRenameWf-suc

TySubstWf-liftˢ :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} →
  TySubstWf Δ Δ′ Ψ σ →
  TySubstWf Δ Δ′ (suc Ψ) (liftSubstˢ σ)
TySubstWf-liftˢ hσ X<Δ =
  renameˢ-preserves-WfTy (hσ X<Δ) SealRenameWf-suc

substᵗ-preserves-WfTy :
  ∀ {Δ Δ′ Ψ} {σ : Substᵗ} {A : Ty} →
  WfTy Δ Ψ A →
  TySubstWf Δ Δ′ Ψ σ →
  WfTy Δ′ Ψ (substᵗ σ A)
substᵗ-preserves-WfTy (wfVar X<Δ) hσ = hσ X<Δ
substᵗ-preserves-WfTy (wfSeal α<Ψ) hσ = wfSeal α<Ψ
substᵗ-preserves-WfTy wfBase hσ = wfBase
substᵗ-preserves-WfTy wf★ hσ = wf★
substᵗ-preserves-WfTy (wf⇒ hA hB) hσ =
  wf⇒ (substᵗ-preserves-WfTy hA hσ) (substᵗ-preserves-WfTy hB hσ)
substᵗ-preserves-WfTy (wf∀ hA) hσ =
  wf∀ (substᵗ-preserves-WfTy hA (TySubstWf-exts hσ))

------------------------------------------------------------------------
-- Core renaming/substitution infrastructure
------------------------------------------------------------------------

rename-cong :
  ∀{ρ ρ′ : Renameᵗ} →
  ((X : TyVar) → ρ X ≡ ρ′ X) →
  (A : Ty) →
  renameᵗ ρ A ≡ renameᵗ ρ′ A
rename-cong h (＇ X) = cong ＇_ (h X)
rename-cong h (｀ α) = refl
rename-cong h (‵ ι) = refl
rename-cong h ★ = refl
rename-cong h (A ⇒ B) = cong₂ _⇒_ (rename-cong h A) (rename-cong h B)
rename-cong {ρ = ρ} {ρ′ = ρ′} h (`∀ A) = cong `∀ (rename-cong h-ext A)
  where
    h-ext : (X : TyVar) → extᵗ ρ X ≡ extᵗ ρ′ X
    h-ext zero = refl
    h-ext (suc X) = cong suc (h X)

substᵗ-cong :
  ∀
  {σ τ : Substᵗ} →
  ((X : TyVar) → σ X ≡ τ X) →
  (A : Ty) →
  substᵗ σ A ≡ substᵗ τ A
substᵗ-cong h (＇ X) = h X
substᵗ-cong h (｀ α) = refl
substᵗ-cong h (‵ ι) = refl
substᵗ-cong h ★ = refl
substᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-cong h A) (substᵗ-cong h B)
substᵗ-cong {σ = σ} {τ = τ} h (`∀ A) =
  cong `∀ (substᵗ-cong h-ext A)
  where
    h-ext : (X : TyVar) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)

substˢᵗ-cong :
  ∀
  {τ υ : Substˢᵗ} →
  ((α : Seal) → τ α ≡ υ α) →
  (A : Ty) →
  substˢᵗ τ A ≡ substˢᵗ υ A
substˢᵗ-cong h (＇ X) = refl
substˢᵗ-cong h (｀ α) = h α
substˢᵗ-cong h (‵ ι) = refl
substˢᵗ-cong h ★ = refl
substˢᵗ-cong h (A ⇒ B) =
  cong₂ _⇒_ (substˢᵗ-cong h A) (substˢᵗ-cong h B)
substˢᵗ-cong {τ = τ} {υ = υ} h (`∀ A) =
  cong `∀ (substˢᵗ-cong h-ext A)
  where
    h-ext : (α : Seal) → extsˢᵗ τ α ≡ extsˢᵗ υ α
    h-ext α = cong (renameᵗ suc) (h α)

substᵗ-id :
  ∀ (A : Ty) →
  substᵗ (λ X → ＇ X) A ≡ A
substᵗ-id (＇ X) = refl
substᵗ-id (｀ α) = refl
substᵗ-id (‵ ι) = refl
substᵗ-id ★ = refl
substᵗ-id (A ⇒ B) = cong₂ _⇒_ (substᵗ-id A) (substᵗ-id B)
substᵗ-id (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong env-eq A)
      (substᵗ-id A))
  where
    env-eq : (X : TyVar) → extsᵗ (λ Y → ＇ Y) X ≡ ＇ X
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-compose :
  ∀
  (ρ₁ : Renameᵗ) (ρ₂ : Renameᵗ) (A : Ty) →
  renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
renameᵗ-compose ρ₁ ρ₂ (＇ X) = refl
renameᵗ-compose ρ₁ ρ₂ (｀ α) = refl
renameᵗ-compose ρ₁ ρ₂ (‵ ι) = refl
renameᵗ-compose ρ₁ ρ₂ ★ = refl
renameᵗ-compose ρ₁ ρ₂ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-compose ρ₁ ρ₂ A) (renameᵗ-compose ρ₁ ρ₂ B)
renameᵗ-compose ρ₁ ρ₂ (`∀ A) =
  trans
    (cong `∀ (renameᵗ-compose (extᵗ ρ₁) (extᵗ ρ₂) A))
    (cong `∀ (rename-cong ext-comp A))
  where
    ext-comp :
      (X : TyVar) →
      extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X′ → ρ₂ (ρ₁ X′)) X
    ext-comp zero = refl
    ext-comp (suc X) = refl

renameᵗ-suc-comm :
  ∀
  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ suc (renameᵗ ρ A) ≡
  renameᵗ (extᵗ ρ) (renameᵗ suc A)
renameᵗ-suc-comm ρ A =
  trans
    (renameᵗ-compose ρ suc A)
    (sym (renameᵗ-compose suc (extᵗ ρ) A))

substᵗ-renameᵗ :
  ∀
  (ρ : Renameᵗ) (σ : Substᵗ) (A : Ty) →
  substᵗ σ (renameᵗ ρ A) ≡ substᵗ (λ X → σ (ρ X)) A
substᵗ-renameᵗ ρ σ (＇ X) = refl
substᵗ-renameᵗ ρ σ (｀ α) = refl
substᵗ-renameᵗ ρ σ (‵ ι) = refl
substᵗ-renameᵗ ρ σ ★ = refl
substᵗ-renameᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-renameᵗ ρ σ A) (substᵗ-renameᵗ ρ σ B)
substᵗ-renameᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-renameᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      extsᵗ σ (extᵗ ρ X) ≡ extsᵗ (λ Y → σ (ρ Y)) X
    env-eq zero = refl
    env-eq (suc X) = refl

renameᵗ-substᵗ :
  ∀
  (ρ : Renameᵗ) (σ : Substᵗ) (A : Ty) →
  renameᵗ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameᵗ ρ (σ X)) A
renameᵗ-substᵗ ρ σ (＇ X) = refl
renameᵗ-substᵗ ρ σ (｀ α) = refl
renameᵗ-substᵗ ρ σ (‵ ι) = refl
renameᵗ-substᵗ ρ σ ★ = refl
renameᵗ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-substᵗ ρ σ A) (renameᵗ-substᵗ ρ σ B)
renameᵗ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameᵗ-substᵗ (extᵗ ρ) (extsᵗ σ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      renameᵗ (extᵗ ρ) (extsᵗ σ X) ≡ extsᵗ (λ Y → renameᵗ ρ (σ Y)) X
    env-eq zero = refl
    env-eq (suc X) = sym (renameᵗ-suc-comm ρ (σ X))

substᵗ-suc-renameᵗ-suc :
  ∀
  (σ : Substᵗ) (A : Ty) →
  substᵗ (extsᵗ σ) (renameᵗ suc A) ≡
  renameᵗ suc (substᵗ σ A)
substᵗ-suc-renameᵗ-suc σ A =
  trans
    (substᵗ-renameᵗ suc (extsᵗ σ) A)
    (sym (renameᵗ-substᵗ suc σ A))

substᵗ-substᵗ :
  ∀
  (σ : Substᵗ) (τ : Substᵗ) (A : Ty) →
  substᵗ σ (substᵗ τ A) ≡
  substᵗ (λ X → substᵗ σ (τ X)) A
substᵗ-substᵗ σ τ (＇ X) = refl
substᵗ-substᵗ σ τ (｀ α) = refl
substᵗ-substᵗ σ τ (‵ ι) = refl
substᵗ-substᵗ σ τ ★ = refl
substᵗ-substᵗ σ τ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-substᵗ σ τ A) (substᵗ-substᵗ σ τ B)
substᵗ-substᵗ σ τ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-substᵗ (extsᵗ σ) (extsᵗ τ) A)
      (substᵗ-cong env-eq A))
  where
    env-eq :
      (X : TyVar) →
      substᵗ (extsᵗ σ) (extsᵗ τ X) ≡
      extsᵗ (λ Y → substᵗ σ (τ Y)) X
    env-eq zero = refl
    env-eq (suc X) = substᵗ-suc-renameᵗ-suc σ (τ X)

------------------------------------------------------------------------
-- Seal commutation
------------------------------------------------------------------------

renameˢ-renameᵗ :
  ∀
  (ρᵗ : Renameᵗ) (ρˢ : Renameˢ) (A : Ty) →
  renameˢ ρˢ (renameᵗ ρᵗ A) ≡
  renameᵗ ρᵗ (renameˢ ρˢ A)
renameˢ-renameᵗ ρᵗ ρˢ (＇ X) = refl
renameˢ-renameᵗ ρᵗ ρˢ (｀ α) = refl
renameˢ-renameᵗ ρᵗ ρˢ (‵ ι) = refl
renameˢ-renameᵗ ρᵗ ρˢ ★ = refl
renameˢ-renameᵗ ρᵗ ρˢ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-renameᵗ ρᵗ ρˢ A) (renameˢ-renameᵗ ρᵗ ρˢ B)
renameˢ-renameᵗ ρᵗ ρˢ (`∀ A) =
  cong `∀ (renameˢ-renameᵗ (extᵗ ρᵗ) ρˢ A)

renameᵗ-renameˢ :
  ∀
  (ρ : Renameᵗ) (ϱ : Renameˢ) (A : Ty) →
  renameᵗ ρ (renameˢ ϱ A) ≡ renameˢ ϱ (renameᵗ ρ A)
renameᵗ-renameˢ ρ ϱ (＇ X) = refl
renameᵗ-renameˢ ρ ϱ (｀ α) = refl
renameᵗ-renameˢ ρ ϱ (‵ ι) = refl
renameᵗ-renameˢ ρ ϱ ★ = refl
renameᵗ-renameˢ ρ ϱ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-renameˢ ρ ϱ A) (renameᵗ-renameˢ ρ ϱ B)
renameᵗ-renameˢ ρ ϱ (`∀ A) =
  cong `∀ (renameᵗ-renameˢ (extᵗ ρ) ϱ A)

renameˢ-substᵗ :
  ∀
  (ρ : Renameˢ) (σ : Substᵗ) (A : Ty) →
  renameˢ ρ (substᵗ σ A) ≡
  substᵗ (λ X → renameˢ ρ (σ X)) (renameˢ ρ A)
renameˢ-substᵗ ρ σ (＇ X) = refl
renameˢ-substᵗ ρ σ (｀ α) = refl
renameˢ-substᵗ ρ σ (‵ ι) = refl
renameˢ-substᵗ ρ σ ★ = refl
renameˢ-substᵗ ρ σ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-substᵗ ρ σ A) (renameˢ-substᵗ ρ σ B)
renameˢ-substᵗ ρ σ (`∀ A) =
  cong `∀
    (trans
      (renameˢ-substᵗ ρ (extsᵗ σ) A)
      (substᵗ-cong env-eq (renameˢ ρ A)))
  where
    env-eq :
      (X : TyVar) →
      renameˢ ρ (extsᵗ σ X) ≡ extsᵗ (λ Y → renameˢ ρ (σ Y)) X
    env-eq zero = refl
    env-eq (suc X) = sym (renameᵗ-renameˢ suc ρ (σ X))

inst★-renameᵗ-suc :
  ∀ (A : Ty) →
  (renameᵗ suc A) [ ★ ]ᵗ ≡ A
inst★-renameᵗ-suc A =
  trans
    (substᵗ-renameᵗ suc (singleTyEnv ★) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-inst★ :
  ∀
  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ ρ (A [ ★ ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ★ ]ᵗ
renameᵗ-inst★ ρ A =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv ★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv ★) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv ★ X) ≡
      singleTyEnv ★ (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-inst★ :
  ∀
  (σ : Substᵗ) (A : Ty) →
  substᵗ σ (A [ ★ ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ★ ]ᵗ
substᵗ-inst★ σ A =
  trans
    (substᵗ-substᵗ σ (singleTyEnv ★) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv ★) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar) →
      substᵗ σ (singleTyEnv ★ X) ≡ substᵗ (singleTyEnv ★) (extsᵗ σ X)
    env zero = refl
    env (suc X) = sym (inst★-renameᵗ-suc (σ X))

renameˢ-inst★ :
  ∀
  (ρ : Renameˢ) (A : Ty) →
  renameˢ ρ (A [ ★ ]ᵗ) ≡ (renameˢ ρ A) [ ★ ]ᵗ
renameˢ-inst★ ρ A =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv ★) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar) →
      renameˢ ρ (singleTyEnv ★ X) ≡ singleTyEnv ★ X
    env zero = refl
    env (suc X) = refl

------------------------------------------------------------------------
-- Commuting with seal lifting/opening and contexts
------------------------------------------------------------------------

renameᵗ-⇑ˢ :
  ∀  (ρ : Renameᵗ) (B : Ty) →
  renameᵗ ρ (⇑ˢ B) ≡ ⇑ˢ (renameᵗ ρ B)
renameᵗ-⇑ˢ ρ (＇ X) = refl
renameᵗ-⇑ˢ ρ (｀ α) = refl
renameᵗ-⇑ˢ ρ (‵ ι) = refl
renameᵗ-⇑ˢ ρ ★ = refl
renameᵗ-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-⇑ˢ ρ A) (renameᵗ-⇑ˢ ρ B)
renameᵗ-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameᵗ-⇑ˢ (extᵗ ρ) A)

private
  exts-liftSubstˢ :
    ∀
    (σ : Substᵗ) (X : TyVar) →
    extsᵗ (liftSubstˢ σ) X ≡ liftSubstˢ (extsᵗ σ) X
  exts-liftSubstˢ σ zero = refl
  exts-liftSubstˢ σ (suc X) = renameᵗ-⇑ˢ suc (σ X)

substᵗ-⇑ˢ :
  ∀  (σ : Substᵗ) (B : Ty) →
  substᵗ (liftSubstˢ σ) (⇑ˢ B) ≡ ⇑ˢ (substᵗ σ B)
substᵗ-⇑ˢ σ (＇ X) = refl
substᵗ-⇑ˢ σ (｀ α) = refl
substᵗ-⇑ˢ σ (‵ ι) = refl
substᵗ-⇑ˢ σ ★ = refl
substᵗ-⇑ˢ σ (A ⇒ B) =
  cong₂ _⇒_ (substᵗ-⇑ˢ σ A) (substᵗ-⇑ˢ σ B)
substᵗ-⇑ˢ σ (`∀ A) =
  cong `∀
    (trans
      (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
      (substᵗ-⇑ˢ (extsᵗ σ) A))

open-renᵗ-suc :
  
  (A : Ty) →
  (T : Ty) →
  (renameᵗ suc A) [ T ]ᵗ ≡ A
open-renᵗ-suc A T =
  trans
    (substᵗ-renameᵗ suc (singleTyEnv T) A)
    (trans
      (substᵗ-cong (λ X → refl) A)
      (substᵗ-id A))

renameᵗ-[]ᵗ-seal :
  ∀
  (ρ : Renameᵗ) (A : Ty) (α : Seal) →
  renameᵗ ρ (A [ ｀ α ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ ｀ α ]ᵗ
renameᵗ-[]ᵗ-seal ρ A α =
  trans
    (renameᵗ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-renameᵗ (extᵗ ρ) (singleTyEnv (｀ α)) A)))
  where
    env :
      (X : TyVar) →
      renameᵗ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ α) (extᵗ ρ X)
    env zero = refl
    env (suc X) = refl

substᵗ-[]ᵗ-seal :
  ∀
  (σ : Substᵗ) (A : Ty) (α : Seal) →
  substᵗ σ (A [ ｀ α ]ᵗ) ≡ (substᵗ (extsᵗ σ) A) [ ｀ α ]ᵗ
substᵗ-[]ᵗ-seal σ A α =
  trans
    (substᵗ-substᵗ σ (singleTyEnv (｀ α)) A)
    (trans
      (substᵗ-cong env A)
      (sym (substᵗ-substᵗ (singleTyEnv (｀ α)) (extsᵗ σ) A)))
  where
    env :
      (X : TyVar) →
      substᵗ σ (singleTyEnv (｀ α) X) ≡
      substᵗ (singleTyEnv (｀ α)) (extsᵗ σ X)
    env zero = refl
    env (suc X) = sym (open-renᵗ-suc (σ X) (｀ α))

renameˢ-[]ᵗ-seal :
  ∀
  (ρ : Renameˢ) (A : Ty) (α : Seal) →
  renameˢ ρ (A [ ｀ α ]ᵗ) ≡ (renameˢ ρ A) [ ｀ (ρ α) ]ᵗ
renameˢ-[]ᵗ-seal ρ A α =
  trans
    (renameˢ-substᵗ ρ (singleTyEnv (｀ α)) A)
    (substᵗ-cong env (renameˢ ρ A))
  where
    env :
      (X : TyVar) →
      renameˢ ρ (singleTyEnv (｀ α) X) ≡
      singleTyEnv (｀ (ρ α)) X
    env zero = refl
    env (suc X) = refl

renameˢ-ext-⇑ˢ :
  ∀
  (ρ : Renameˢ) (A : Ty) →
  renameˢ (extˢ ρ) (⇑ˢ A) ≡ ⇑ˢ (renameˢ ρ A)
renameˢ-ext-⇑ˢ ρ (＇ X) = refl
renameˢ-ext-⇑ˢ ρ (｀ α) = refl
renameˢ-ext-⇑ˢ ρ (‵ ι) = refl
renameˢ-ext-⇑ˢ ρ ★ = refl
renameˢ-ext-⇑ˢ ρ (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-ext-⇑ˢ ρ A) (renameˢ-ext-⇑ˢ ρ B)
renameˢ-ext-⇑ˢ ρ (`∀ A) =
  cong `∀ (renameˢ-ext-⇑ˢ ρ A)

renameᵗ-ν-src :
  ∀  (ρ : Renameᵗ) (A : Ty) →
  renameᵗ ρ ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡
  (⇑ˢ (renameᵗ (extᵗ ρ) A)) [ ｀ zero ]ᵗ
renameᵗ-ν-src ρ A =
  trans
    (renameᵗ-[]ᵗ-seal ρ (⇑ˢ A) zero)
    (cong (λ C → C [ ｀ zero ]ᵗ) (renameᵗ-⇑ˢ (extᵗ ρ) A))

substᵗ-ν-src :
  ∀  (σ : Substᵗ) (A : Ty) →
  substᵗ (liftSubstˢ σ) ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡
  (⇑ˢ (substᵗ (extsᵗ σ) A)) [ ｀ zero ]ᵗ
substᵗ-ν-src σ A =
  trans
    (substᵗ-[]ᵗ-seal (liftSubstˢ σ) (⇑ˢ A) zero)
    (cong
      (λ C → C [ ｀ zero ]ᵗ)
      (trans
        (substᵗ-cong (exts-liftSubstˢ σ) (⇑ˢ A))
        (substᵗ-⇑ˢ (extsᵗ σ) A)))

renameˢ-ν-src :
  ∀  (ρ : Renameˢ) (A : Ty) →
  renameˢ (extˢ ρ) ((⇑ˢ A) [ ｀ zero ]ᵗ) ≡
  (⇑ˢ (renameˢ ρ A)) [ ｀ zero ]ᵗ
renameˢ-ν-src ρ A =
  trans
    (renameˢ-[]ᵗ-seal (extˢ ρ) (⇑ˢ A) zero)
    (cong (λ C → C [ ｀ zero ]ᵗ) (renameˢ-ext-⇑ˢ ρ A))

------------------------------------------------------------------------
-- Useful seal-opening identity (used by Store.agda)
------------------------------------------------------------------------

renameˢ-single-⇑ˢ-id :
  
  (α : Seal) →
  (A : Ty) →
  renameˢ (singleSealEnv α) (⇑ˢ A) ≡ A
renameˢ-single-⇑ˢ-id α (＇ X) = refl
renameˢ-single-⇑ˢ-id α (｀ β) = refl
renameˢ-single-⇑ˢ-id α (‵ ι) = refl
renameˢ-single-⇑ˢ-id α ★ = refl
renameˢ-single-⇑ˢ-id α (A ⇒ B) =
  cong₂ _⇒_ (renameˢ-single-⇑ˢ-id α A) (renameˢ-single-⇑ˢ-id α B)
renameˢ-single-⇑ˢ-id α (`∀ A) =
  cong `∀ (renameˢ-single-⇑ˢ-id α A)
