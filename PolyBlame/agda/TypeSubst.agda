module TypeSubst where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (cong; cong₂; sym; trans)
open import Data.List using ([]; _∷_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Base using (_<_; z<s; s<s)
open import Types

infixr 50 _⨟ᵗ_
_⨟ᵗ_ : Substᵗ → Substᵗ → Substᵗ
(σ₁ ⨟ᵗ σ₂) i = substᵗ σ₂ (σ₁ i)

subst-one-at-one : Ty → Ty → Ty
subst-one-at-one A B = substᵗ (extsᵗ (singleTyEnv B)) A

single-subst-def : (A B : Ty) →
  A [ B ]ᵗ ≡ substᵗ (singleTyEnv B) A
single-subst-def A B = refl

subst-one-at-one-def : (A B : Ty) →
  subst-one-at-one A B ≡ substᵗ (extsᵗ (singleTyEnv B)) A
subst-one-at-one-def A B = refl

------------------------------------------------------------------------
-- Congruence helpers
------------------------------------------------------------------------

rename-cong : ∀ {ρ ρ' : Renameᵗ} → ((X : ℕ) → ρ X ≡ ρ' X) → (A : Ty) →
  renameᵗ ρ A ≡ renameᵗ ρ' A
rename-cong {ρ} {ρ'} h (＇ X)   = cong (λ X' → ＇ X') (h X)
rename-cong {ρ} {ρ'} h (｀ α)   = refl
rename-cong {ρ} {ρ'} h (‵ ι)   = refl
rename-cong {ρ} {ρ'} h `★       = refl
rename-cong {ρ} {ρ'} h (A ⇒ B)  = cong₂ _⇒_ (rename-cong h A) (rename-cong h B)
rename-cong {ρ} {ρ'} h (`∀ A)   = cong `∀ (rename-cong h-ext A)
  where
    h-ext : (X : ℕ) → extᵗ ρ X ≡ extᵗ ρ' X
    h-ext zero    = refl
    h-ext (suc X) = cong suc (h X)

renameˢ-cong : ∀ {ρ ρ' : Renameˢ} → ((α : Seal) → ρ α ≡ ρ' α) → (A : Ty) →
  renameˢ ρ A ≡ renameˢ ρ' A
renameˢ-cong {ρ} {ρ'} h (＇ X)   = refl
renameˢ-cong {ρ} {ρ'} h (｀ α)   = cong (λ α' → ｀ α') (h α)
renameˢ-cong {ρ} {ρ'} h (‵ ι)   = refl
renameˢ-cong {ρ} {ρ'} h `★       = refl
renameˢ-cong {ρ} {ρ'} h (A ⇒ B)  = cong₂ _⇒_ (renameˢ-cong h A) (renameˢ-cong h B)
renameˢ-cong {ρ} {ρ'} h (`∀ A)   = cong `∀ (renameˢ-cong h A)

subst-cong : ∀ {σ τ : Substᵗ} → ((X : ℕ) → σ X ≡ τ X) → (A : Ty) →
  substᵗ σ A ≡ substᵗ τ A
subst-cong {σ} {τ} h (＇ X)   = h X
subst-cong {σ} {τ} h (｀ α)   = refl
subst-cong {σ} {τ} h (‵ ι)   = refl
subst-cong {σ} {τ} h `★       = refl
subst-cong {σ} {τ} h (A ⇒ B)  = cong₂ _⇒_ (subst-cong h A) (subst-cong h B)
subst-cong {σ} {τ} h (`∀ A)   = cong `∀ (subst-cong h-ext A)
  where
    h-ext : (X : ℕ) → extsᵗ σ X ≡ extsᵗ τ X
    h-ext zero    = refl
    h-ext (suc X) = cong (renameᵗ suc) (h X)

------------------------------------------------------------------------
-- Renaming/substitution interaction
------------------------------------------------------------------------

ext-comp : (ρ₁ ρ₂ : Renameᵗ) →
  ((X : ℕ) → extᵗ ρ₂ (extᵗ ρ₁ X) ≡ extᵗ (λ X' → ρ₂ (ρ₁ X')) X)
ext-comp ρ₁ ρ₂ zero    = refl
ext-comp ρ₁ ρ₂ (suc X) = refl

extˢ-comp : (ρ₁ ρ₂ : Renameˢ) →
  ((α : Seal) → extˢ ρ₂ (extˢ ρ₁ α) ≡ extˢ (λ α' → ρ₂ (ρ₁ α')) α)
extˢ-comp ρ₁ ρ₂ zero    = refl
extˢ-comp ρ₁ ρ₂ (suc α) = refl

rename-rename-commute : (ρ₁ ρ₂ : Renameᵗ) → (A : Ty) →
  renameᵗ ρ₂ (renameᵗ ρ₁ A) ≡ renameᵗ (λ X → ρ₂ (ρ₁ X)) A
rename-rename-commute ρ₁ ρ₂ (＇ X)   = refl
rename-rename-commute ρ₁ ρ₂ (｀ α)   = refl
rename-rename-commute ρ₁ ρ₂ (‵ ι)   = refl
rename-rename-commute ρ₁ ρ₂ `★       = refl
rename-rename-commute ρ₁ ρ₂ (A ⇒ B)  =
  cong₂ _⇒_ (rename-rename-commute ρ₁ ρ₂ A) (rename-rename-commute ρ₁ ρ₂ B)
rename-rename-commute ρ₁ ρ₂ (`∀ A)   =
  trans
    (cong `∀ (rename-rename-commute (extᵗ ρ₁) (extᵗ ρ₂) A))
    (cong `∀ (rename-cong (ext-comp ρ₁ ρ₂) A))

renameˢ-rename-commute : (ρ₁ ρ₂ : Renameˢ) → (A : Ty) →
  renameˢ ρ₂ (renameˢ ρ₁ A) ≡ renameˢ (λ α → ρ₂ (ρ₁ α)) A
renameˢ-rename-commute ρ₁ ρ₂ (＇ X)   = refl
renameˢ-rename-commute ρ₁ ρ₂ (｀ α)   = refl
renameˢ-rename-commute ρ₁ ρ₂ (‵ ι)   = refl
renameˢ-rename-commute ρ₁ ρ₂ `★       = refl
renameˢ-rename-commute ρ₁ ρ₂ (A ⇒ B)  =
  cong₂ _⇒_ (renameˢ-rename-commute ρ₁ ρ₂ A) (renameˢ-rename-commute ρ₁ ρ₂ B)
renameˢ-rename-commute ρ₁ ρ₂ (`∀ A)   = cong `∀ (renameˢ-rename-commute ρ₁ ρ₂ A)

renameᵗ-renameˢ :
  {ρ : Renameᵗ} {ϱ : Renameˢ} {A : Ty} →
  renameᵗ ρ (renameˢ ϱ A) ≡ renameˢ ϱ (renameᵗ ρ A)
renameᵗ-renameˢ {ρ} {ϱ} {＇ X} = refl
renameᵗ-renameˢ {ρ} {ϱ} {｀ α} = refl
renameᵗ-renameˢ {ρ} {ϱ} {‵ ι} = refl
renameᵗ-renameˢ {ρ} {ϱ} {`★} = refl
renameᵗ-renameˢ {ρ} {ϱ} {A ⇒ B} =
  cong₂ _⇒_
    (renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} {A = A})
    (renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} {A = B})
renameᵗ-renameˢ {ρ} {ϱ} {`∀ A} =
  cong (λ A' → `∀ A') (renameᵗ-renameˢ {ρ = extᵗ ρ} {ϱ = ϱ} {A = A})

map-renameᵗ-renameˢ :
  {ρ : Renameᵗ} {ϱ : Renameˢ} →
  (Γ : Ctx) →
  map (renameˢ ϱ) (map (renameᵗ ρ) Γ) ≡ map (renameᵗ ρ) (map (renameˢ ϱ) Γ)
map-renameᵗ-renameˢ [] = refl
map-renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} (A ∷ Γ) =
  cong₂ _∷_
    (sym (renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} {A = A}))
    (map-renameᵗ-renameˢ {ρ = ρ} {ϱ = ϱ} Γ)

------------------------------------------------------------------------
-- Store lookup and renaming preservation for well-formed types
------------------------------------------------------------------------

lookupˢ-map-inv :
  {stores : Store} {α : Seal} {B : Ty} {ρ : Renameᵗ} →
  renameStoreᵗ ρ stores ∋ˢ α ⦂ B →
  Σ Ty (λ A → Σ (stores ∋ˢ α ⦂ A) (λ _ → B ≡ renameᵗ ρ A))
lookupˢ-map-inv {stores = A₀ ∷ stores} {α = zero} Zˢ = A₀ , (Zˢ , refl)
lookupˢ-map-inv {stores = _ ∷ stores} {α = suc α} (Sˢ h) with lookupˢ-map-inv h
... | A , (hA , eq) = A , (Sˢ hA , eq)

lookupˢ-map-renameᵗ :
  {Σ : Store} {α : Seal} {A : Ty} {ρ : Renameᵗ} →
  Σ ∋ˢ α ⦂ A →
  renameStoreᵗ ρ Σ ∋ˢ α ⦂ renameᵗ ρ A
lookupˢ-map-renameᵗ Zˢ = Zˢ
lookupˢ-map-renameᵗ (Sˢ h) = Sˢ (lookupˢ-map-renameᵗ h)

map-renameStore-suc : (ρ : Renameᵗ) (Σ : Store) →
  renameStoreᵗ (extᵗ ρ) (renameStoreᵗ suc Σ) ≡
  renameStoreᵗ suc (renameStoreᵗ ρ Σ)
map-renameStore-suc ρ [] = refl
map-renameStore-suc ρ (A ∷ Σ) =
  cong₂ _∷_
    (trans
      (rename-rename-commute suc (extᵗ ρ) A)
      (trans
        (rename-cong (λ X → refl) A)
        (sym (rename-rename-commute ρ suc A))))
    (map-renameStore-suc ρ Σ)

TyRenameWf : TyCtx → TyCtx → Renameᵗ → Set
TyRenameWf Δ Δ' ρ = ∀ {X} → X < Δ → ρ X < Δ'

TyRenameWf-ext :
  {Δ Δ' : TyCtx} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  TyRenameWf (suc Δ) (suc Δ') (extᵗ ρ)
TyRenameWf-ext hρ {zero} z<s = z<s
TyRenameWf-ext hρ {suc X} (s<s x<Δ) = s<s (hρ {X} x<Δ)

renameᵗ-preserves-WfTy :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {ρ : Renameᵗ} →
  WfTy Δ Σ A →
  TyRenameWf Δ Δ' ρ →
  WfTy Δ' (renameStoreᵗ ρ Σ) (renameᵗ ρ A)
renameᵗ-preserves-WfTy (wfX x<Δ) hρ = wfX (hρ x<Δ)
renameᵗ-preserves-WfTy wfι hρ = wfι
renameᵗ-preserves-WfTy wf★ hρ = wf★
renameᵗ-preserves-WfTy (wfα h) hρ = wfα (lookupˢ-map-renameᵗ h)
renameᵗ-preserves-WfTy (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy hA hρ) (renameᵗ-preserves-WfTy hB hρ)
renameᵗ-preserves-WfTy {Δ' = Δ'} {Σ = Σ} {ρ = ρ} (wf∀ {A = A} hA) hρ =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc Δ') S (renameᵗ (extᵗ ρ) A))
      (map-renameStore-suc ρ Σ)
      (renameᵗ-preserves-WfTy hA (TyRenameWf-ext hρ)))

renameᵗ-preserves-WfTy↑ :
  {Δ Δ' : TyCtx} {Σ : Store} {A : Ty} {ρ : Renameᵗ} →
  WfTy (suc Δ) Σ A →
  TyRenameWf Δ Δ' ρ →
  WfTy (suc Δ') (renameStoreᵗ ρ Σ) (renameᵗ (extᵗ ρ) A)
renameᵗ-preserves-WfTy↑ (wfX x<) hρ = wfX (TyRenameWf-ext hρ x<)
renameᵗ-preserves-WfTy↑ wfι hρ = wfι
renameᵗ-preserves-WfTy↑ wf★ hρ = wf★
renameᵗ-preserves-WfTy↑ (wfα h) hρ = wfα (lookupˢ-map-renameᵗ h)
renameᵗ-preserves-WfTy↑ (wf⇒ hA hB) hρ =
  wf⇒ (renameᵗ-preserves-WfTy↑ hA hρ) (renameᵗ-preserves-WfTy↑ hB hρ)
renameᵗ-preserves-WfTy↑ {Δ' = Δ'} {Σ = Σ} {ρ = ρ} (wf∀ {A = A} hA) hρ =
  wf∀
    (Eq.subst
      (λ S → WfTy (suc (suc Δ')) S (renameᵗ (extᵗ (extᵗ ρ)) A))
      (map-renameStore-suc ρ Σ)
      (renameᵗ-preserves-WfTy↑ hA (TyRenameWf-ext hρ)))

exts-ext-comp : (ρ : Renameᵗ) → (τ : Substᵗ) →
  ((X : ℕ) → extsᵗ τ (extᵗ ρ X) ≡ extsᵗ (λ X' → τ (ρ X')) X)
exts-ext-comp ρ τ zero    = refl
exts-ext-comp ρ τ (suc X) = refl

rename-subst-commute : (ρ : Renameᵗ) → (τ : Substᵗ) → (A : Ty) →
  substᵗ τ (renameᵗ ρ A) ≡ substᵗ (λ X → τ (ρ X)) A
rename-subst-commute ρ τ (＇ X)   = refl
rename-subst-commute ρ τ (｀ α)   = refl
rename-subst-commute ρ τ (‵ ι)   = refl
rename-subst-commute ρ τ `★       = refl
rename-subst-commute ρ τ (A ⇒ B)  =
  cong₂ _⇒_ (rename-subst-commute ρ τ A) (rename-subst-commute ρ τ B)
rename-subst-commute ρ τ (`∀ A)   =
  trans
    (cong `∀ (rename-subst-commute (extᵗ ρ) (extsᵗ τ) A))
    (cong `∀ (subst-cong (exts-ext-comp ρ τ) A))

ext-exts-comp : (ρ : Renameᵗ) → (τ : Substᵗ) →
  ((X : ℕ) → renameᵗ (extᵗ ρ) (extsᵗ τ X) ≡ extsᵗ (λ X' → renameᵗ ρ (τ X')) X)
ext-exts-comp ρ τ zero    = refl
ext-exts-comp ρ τ (suc X) =
  trans
    (rename-rename-commute suc (extᵗ ρ) (τ X))
    (trans
      (rename-cong (λ X' → refl) (τ X))
      (sym (rename-rename-commute ρ suc (τ X))))

rename-subst : (ρ : Renameᵗ) → (τ : Substᵗ) → (A : Ty) →
  renameᵗ ρ (substᵗ τ A) ≡ substᵗ (λ X → renameᵗ ρ (τ X)) A
rename-subst ρ τ (＇ X)   = refl
rename-subst ρ τ (｀ α)   = refl
rename-subst ρ τ (‵ ι)   = refl
rename-subst ρ τ `★       = refl
rename-subst ρ τ (A ⇒ B)  =
  cong₂ _⇒_ (rename-subst ρ τ A) (rename-subst ρ τ B)
rename-subst ρ τ (`∀ A)   =
  trans
    (cong `∀ (rename-subst (extᵗ ρ) (extsᵗ τ) A))
    (cong `∀ (subst-cong (ext-exts-comp ρ τ) A))

rename-[]ᵗ-commute : (ρ : Renameᵗ) (A B : Ty) →
  renameᵗ ρ (A [ B ]ᵗ) ≡ (renameᵗ (extᵗ ρ) A) [ renameᵗ ρ B ]ᵗ
rename-[]ᵗ-commute ρ A B =
  trans
    (trans
      (cong (renameᵗ ρ) (single-subst-def A B))
      (rename-subst ρ (singleTyEnv B) A))
    (trans
      (subst-cong env-eq A)
      (sym (rename-subst-commute (extᵗ ρ) (singleTyEnv (renameᵗ ρ B)) A)))
  where
    env-eq : (i : Var) →
      (λ j → renameᵗ ρ (singleTyEnv B j)) i ≡
      (λ j → singleTyEnv (renameᵗ ρ B) (extᵗ ρ j)) i
    env-eq zero = refl
    env-eq (suc i) = refl

renameˢ-substᵗ-commute :
  (ρ : Renameˢ) (σ : Substᵗ) (A : Ty) →
  renameˢ ρ (substᵗ σ A) ≡ substᵗ (λ X → renameˢ ρ (σ X)) (renameˢ ρ A)
renameˢ-substᵗ-commute ρ σ (＇ X) = refl
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
    env-eq : (X : Var) →
      renameˢ ρ (extsᵗ σ X) ≡ extsᵗ (λ X' → renameˢ ρ (σ X')) X
    env-eq zero = refl
    env-eq (suc X) =
      sym (renameᵗ-renameˢ {ρ = suc} {ϱ = ρ} {A = σ X})

renameˢ-[]ᵗ-commute :
  (ρ : Renameˢ) (A : Ty) (α : Seal) →
  renameˢ ρ (A [ ｀ α ]ᵗ) ≡ (renameˢ ρ A) [ ｀ (ρ α) ]ᵗ
renameˢ-[]ᵗ-commute ρ A α =
  trans
    (renameˢ-substᵗ-commute ρ (singleTyEnv (｀ α)) A)
    (subst-cong env-eq (renameˢ ρ A))
  where
    env-eq : (X : Var) →
      (λ X' → renameˢ ρ (singleTyEnv (｀ α) X')) X ≡
      (λ X' → singleTyEnv (｀ (ρ α)) X') X
    env-eq zero = refl
    env-eq (suc X) = refl

renameˢ-commute-suc :
  (ρ : Renameˢ) (A : Ty) →
  renameˢ (extˢ ρ) (renameˢ suc A) ≡ renameˢ suc (renameˢ ρ A)
renameˢ-commute-suc ρ A =
  trans
    (renameˢ-rename-commute suc (extˢ ρ) A)
    (trans
      (renameˢ-cong (λ i → refl) A)
      (sym (renameˢ-rename-commute ρ suc A)))

map-renameˢ-commute-suc :
  (ρ : Renameˢ) (Γ : Ctx) →
  map (renameˢ (extˢ ρ)) (map (renameˢ suc) Γ) ≡
  map (renameˢ suc) (map (renameˢ ρ) Γ)
map-renameˢ-commute-suc ρ [] = refl
map-renameˢ-commute-suc ρ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-commute-suc ρ A)
    (map-renameˢ-commute-suc ρ Γ)

map-renameˢ-rename-commute :
  (ρ₁ ρ₂ : Renameˢ) (Γ : Ctx) →
  map (renameˢ ρ₂) (map (renameˢ ρ₁) Γ) ≡
  map (renameˢ (λ α → ρ₂ (ρ₁ α))) Γ
map-renameˢ-rename-commute ρ₁ ρ₂ [] = refl
map-renameˢ-rename-commute ρ₁ ρ₂ (A ∷ Γ) =
  cong₂ _∷_
    (renameˢ-rename-commute ρ₁ ρ₂ A)
    (map-renameˢ-rename-commute ρ₁ ρ₂ Γ)

singleSealEnv-suc-cancel :
  (α : Seal) (A : Ty) →
  renameˢ (singleSealEnv α) (renameˢ suc A) ≡ A
singleSealEnv-suc-cancel α (＇ X) = refl
singleSealEnv-suc-cancel α (｀ β) = refl
singleSealEnv-suc-cancel α (‵ ι) = refl
singleSealEnv-suc-cancel α `★ = refl
singleSealEnv-suc-cancel α (A ⇒ B) =
  cong₂ _⇒_
    (singleSealEnv-suc-cancel α A)
    (singleSealEnv-suc-cancel α B)
singleSealEnv-suc-cancel α (`∀ A) =
  cong `∀ (singleSealEnv-suc-cancel α A)

singleSealEnv-source-eq :
  (α : Seal) (A : Ty) →
  renameˢ (singleSealEnv α) (((renameˢ suc A) [ ｀ zero ]ᵗ)) ≡ A [ ｀ α ]ᵗ
singleSealEnv-source-eq α A =
  trans
    (renameˢ-substᵗ-commute (singleSealEnv α) (singleTyEnv (｀ zero)) (renameˢ suc A))
    (trans
      (subst-cong env-eq (renameˢ (singleSealEnv α) (renameˢ suc A)))
      (trans
        (cong (substᵗ (singleTyEnv (｀ α)))
              (singleSealEnv-suc-cancel α A))
        (sym (single-subst-def A (｀ α)))))
  where
    env-eq : (X : Var) →
      (λ X' → renameˢ (singleSealEnv α) (singleTyEnv (｀ zero) X')) X ≡
      singleTyEnv (｀ α) X
    env-eq zero = refl
    env-eq (suc X) = refl

exts-seq : (σ τ : Substᵗ) →
  ((X : ℕ) → ((extsᵗ σ) ⨟ᵗ (extsᵗ τ)) X ≡ extsᵗ (σ ⨟ᵗ τ) X)
exts-seq σ τ zero    = refl
exts-seq σ τ (suc X) =
  trans
    (rename-subst-commute suc (extsᵗ τ) (σ X))
    (sym (rename-subst suc τ (σ X)))

sub-sub : (σ τ : Substᵗ) → (A : Ty) →
  substᵗ τ (substᵗ σ A) ≡ substᵗ (σ ⨟ᵗ τ) A
sub-sub σ τ (＇ X)   = refl
sub-sub σ τ (｀ α)   = refl
sub-sub σ τ (‵ ι)   = refl
sub-sub σ τ `★       = refl
sub-sub σ τ (A ⇒ B)  = cong₂ _⇒_ (sub-sub σ τ A) (sub-sub σ τ B)
sub-sub σ τ (`∀ A)   =
  trans
    (cong `∀ (sub-sub (extsᵗ σ) (extsᵗ τ) A))
    (cong `∀ (subst-cong (exts-seq σ τ) A))

subst-id : (A : Ty) → substᵗ ＇_ A ≡ A
subst-id (＇ X)   = refl
subst-id (｀ α)   = refl
subst-id (‵ ι)   = refl
subst-id `★       = refl
subst-id (A ⇒ B)  = cong₂ _⇒_ (subst-id A) (subst-id B)
subst-id (`∀ A)   = trans (cong `∀ (subst-cong exts-var A)) (cong `∀ (subst-id A))
  where
    exts-var : (X : ℕ) → extsᵗ ＇_ X ≡ ＇ X
    exts-var zero    = refl
    exts-var (suc X) = refl
