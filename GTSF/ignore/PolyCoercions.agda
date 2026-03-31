module PolyCoercions where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Bool using (Bool)
open import Data.Product using (Σ-syntax; ∃-syntax; _×_; proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import PolyTypes public
open import TypeSubst

------------------------------------------------------------------------
-- Coercions (Fig. 1)
------------------------------------------------------------------------

infixr 7 _↦_
infixr 7 ∀ᶜ_
infixr 6 _⨟_
infixr 6 _`?_
infixr 6 _!

data Coercion : Set where
  idᶜ : Ty → Coercion
  _!  : Ty → Coercion
  _`?_ : Ty → Label → Coercion
  _⁻ : Name → Coercion
  _⁺ : Name → Coercion
  _↦_ : Coercion → Coercion → Coercion
  ∀ᶜ_ : Coercion → Coercion
  _⨟_ : Coercion → Coercion → Coercion
  ⊥ᶜ_⦂_⇨_ : Label → Ty → Ty → Coercion

------------------------------------------------------------------------
-- Coercion typing (Fig. 2)
------------------------------------------------------------------------

infix 4 _∣_⊢_⦂_⇨_

data _∣_⊢_⦂_⇨_ (Σ : Store) (Δ : TyCtx) : Coercion → Ty → Ty → Set where
  ⊢idᶜ : ∀ {A}
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G ! ⦂ G ⇨ `★

  ⊢? : ∀ {G p}
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G `? p ⦂ `★ ⇨ G

  ⊢↦ : ∀ {A A′ B B′ c d}
    → Σ ∣ Δ ⊢ c ⦂ A′ ⇨ A
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ B′
    → Σ ∣ Δ ⊢ c ↦ d ⦂ (A ⇒ B) ⇨ (A′ ⇒ B′)

  ⊢⨟ : ∀ {A B C c d}
    → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ d ⦂ B ⇨ C
    → Σ ∣ Δ ⊢ c ⨟ d ⦂ A ⇨ C

  ⊢conceal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁻ ⦂ A ⇨ `U U

  ⊢reveal : ∀ {U A}
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁺ ⦂ `U U ⇨ A

  ⊢∀ᶜ : ∀ {A B c}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ ∀ᶜ c ⦂ `∀ A ⇨ `∀ B

  ⊢⊥ : ∀ {p A B}
    → WfTy Δ Σ A
    → WfTy Δ Σ B
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⦂ A ⇨ B

coerce : Label → ∀ {A B} → A ~ B → Coercion
coerce p (~-X {X = X}) = idᶜ (` X)
coerce p ~-ℕ = idᶜ `ℕ
coerce p ~-Bool = idᶜ `Bool
coerce p ~-Str = idᶜ `Str
coerce p ~-★ = idᶜ `★
coerce p (~-U {U = U}) = idᶜ (`U U)
coerce p ★~ℕ = `ℕ `? p
coerce p ℕ~★ = `ℕ !
coerce p ★~Bool = `Bool `? p
coerce p Bool~★ = `Bool !
coerce p ★~Str = `Str `? p
coerce p Str~★ = `Str !
coerce p (★~U {U = U}) = (`U U) `? p
coerce p (U~★ {U = U}) = (`U U) !
coerce p (★~⇒ c d) = ((`★ ⇒ `★) `? p) ⨟ (coerce p c ↦ coerce p d)
coerce p (⇒~★ c d) = (coerce p c ↦ coerce p d) ⨟ ((`★ ⇒ `★) !)
coerce p (★~∀ c) = ((`∀ `★) `? p) ⨟ (∀ᶜ (coerce p c))
coerce p (∀~★ c) = (∀ᶜ (coerce p c)) ⨟ ((`∀ `★) !)
coerce p (~-⇒ c d) = coerce p c ↦ coerce p d
coerce p (~-∀ c) = ∀ᶜ (coerce p c)

coercion-type-unique : ∀{Σ Δ} {c A B C D}
  → Σ ∣ Δ ⊢ c ⦂ A ⇨ B
  → Σ ∣ Δ ⊢ c ⦂ C ⇨ D
    -------------
  → A ≡ C × B ≡ D
coercion-type-unique (⊢idᶜ hA) (⊢idᶜ hA′) = refl , refl
coercion-type-unique (⊢! hG gG) (⊢! hG′ gG′) = refl , refl
coercion-type-unique (⊢? hG gG) (⊢? hG′ gG′) = refl , refl
coercion-type-unique (⊢↦ cwt dwt) (⊢↦ cwt′ dwt′)
  with coercion-type-unique cwt cwt′ | coercion-type-unique dwt dwt′
... | refl , refl | refl , refl = refl , refl
coercion-type-unique (⊢⨟ cwt dwt) (⊢⨟ cwt′ dwt′)
  with coercion-type-unique cwt cwt′ | coercion-type-unique dwt dwt′
... | refl , refl | refl , refl = refl , refl
coercion-type-unique (⊢conceal hU) (⊢conceal hU′)
  with ∋ᵁ-unique hU hU′
... | refl = refl , refl
coercion-type-unique (⊢reveal hU) (⊢reveal hU′)
  with ∋ᵁ-unique hU hU′
... | refl = refl , refl
coercion-type-unique (⊢∀ᶜ cwt) (⊢∀ᶜ cwt′)
  with coercion-type-unique cwt cwt′
... | refl , refl = refl , refl
coercion-type-unique (⊢⊥ hA hB) (⊢⊥ hA′ hB′) = refl , refl

injᶜ : Ty → Coercion
injᶜ `★ = idᶜ `★
injᶜ A  = A !

projᶜ : Ty → Label → Coercion
projᶜ `★ p = idᶜ `★
projᶜ A  p = A `? p

renameᶜᵗ : Renameᵗ → Coercion → Coercion
renameᶜᵗ ρ (idᶜ A)            = idᶜ (renameᵗ ρ A)
renameᶜᵗ ρ (G !)              = renameᵗ ρ G !
renameᶜᵗ ρ (G `? p)           = renameᵗ ρ G `? p
renameᶜᵗ ρ (U ⁻)              = U ⁻
renameᶜᵗ ρ (U ⁺)              = U ⁺
renameᶜᵗ ρ (c ↦ d)            = renameᶜᵗ ρ c ↦ renameᶜᵗ ρ d
renameᶜᵗ ρ (∀ᶜ c)             = ∀ᶜ (renameᶜᵗ (extᵗ ρ) c)
renameᶜᵗ ρ (c ⨟ d)            = renameᶜᵗ ρ c ⨟ renameᶜᵗ ρ d
renameᶜᵗ ρ (⊥ᶜ p ⦂ A ⇨ B)     = ⊥ᶜ p ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B

substᶜᵗ : Substᵗ → Coercion → Coercion
substᶜᵗ σ (idᶜ A)            = idᶜ (substᵗ σ A)
substᶜᵗ σ (G !)              = substᵗ σ G !
substᶜᵗ σ (G `? p)           = substᵗ σ G `? p
substᶜᵗ σ (U ⁻)              = U ⁻
substᶜᵗ σ (U ⁺)              = U ⁺
substᶜᵗ σ (c ↦ d)            = substᶜᵗ σ c ↦ substᶜᵗ σ d
substᶜᵗ σ (∀ᶜ c)             = ∀ᶜ (substᶜᵗ (extsᵗ σ) c)
substᶜᵗ σ (c ⨟ d)            = substᶜᵗ σ c ⨟ substᶜᵗ σ d
substᶜᵗ σ (⊥ᶜ p ⦂ A ⇨ B)     = ⊥ᶜ p ⦂ substᵗ σ A ⇨ substᵗ σ B

substᶜᵘ : Name → Coercion → Coercion
substᶜᵘ U c = substᶜᵗ (singleTyEnv (`U U)) c

------------------------------------------------------------------------
-- Coercion renaming and substitution preserves types
------------------------------------------------------------------------

renameᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {ρ : Renameᵗ} →
  TyRenameWf Δ Δ' ρ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  renameΣ ρ Σ ∣ Δ' ⊢ renameᶜᵗ ρ c ⦂ renameᵗ ρ A ⇨ renameᵗ ρ B
renameᶜᵗ-preserves-typing hρ (⊢idᶜ hA) =
  ⊢idᶜ
    (renameᵗ-preserves-WfTy hA hρ)
renameᶜᵗ-preserves-typing hρ (⊢! hG gG) =
  ⊢!
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢? hG gG) =
  ⊢?
    (renameᵗ-preserves-WfTy hG hρ)
    (renameᵗ-preserves-Ground gG)
renameᶜᵗ-preserves-typing hρ (⊢↦ cwt dwt) =
  ⊢↦
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢⨟ cwt dwt) =
  ⊢⨟
    (renameᶜᵗ-preserves-typing hρ cwt)
    (renameᶜᵗ-preserves-typing hρ dwt)
renameᶜᵗ-preserves-typing hρ (⊢conceal hU) =
  ⊢conceal
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing hρ (⊢reveal hU) =
  ⊢reveal
    (lookupᵁ-map-renameᵗ hU)
renameᶜᵗ-preserves-typing {Σ = Σ} {Δ' = Δ'} {ρ = ρ} hρ (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (Eq.subst
      (λ S → S ∣ suc Δ' ⊢ renameᶜᵗ (extᵗ ρ) c ⦂ renameᵗ (extᵗ ρ) A ⇨ renameᵗ (extᵗ ρ) B)
      (map-renameΣ-suc ρ Σ)
      (renameᶜᵗ-preserves-typing
        {Σ = renameΣ suc Σ}
        {ρ = extᵗ ρ}
        (TyRenameWf-ext hρ)
        cwt))
renameᶜᵗ-preserves-typing hρ (⊢⊥ hA hB) =
  ⊢⊥
    (renameᵗ-preserves-WfTy hA hρ)
    (renameᵗ-preserves-WfTy hB hρ)

substᶜᵗ-preserves-typing :
  {Σ : Store} {Δ Δ' : TyCtx} {c : Coercion} {A B : Ty} {σ : Substᵗ} →
  WfStore Σ →
  TySubstWf Δ Δ' Σ σ →
  TySubstIsVar σ →
  Σ ∣ Δ ⊢ c ⦂ A ⇨ B →
  Σ ∣ Δ' ⊢ substᶜᵗ σ c ⦂ substᵗ σ A ⇨ substᵗ σ B
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢idᶜ hA) =
  ⊢idᶜ
    (substᵗ-preserves-WfTy hA hσ)
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢! hG gG) =
  ⊢!
    (substᵗ-preserves-WfTy hG hσ)
    (substᵗ-preserves-Ground gG hσv)
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢? hG gG) =
  ⊢?
    (substᵗ-preserves-WfTy hG hσ)
    (substᵗ-preserves-Ground gG hσv)
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢↦ cwt dwt) =
  ⊢↦
    (substᶜᵗ-preserves-typing wfΣ hσ hσv cwt)
    (substᶜᵗ-preserves-typing wfΣ hσ hσv dwt)
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢⨟ cwt dwt) =
  ⊢⨟
    (substᶜᵗ-preserves-typing wfΣ hσ hσv cwt)
    (substᶜᵗ-preserves-typing wfΣ hσ hσv dwt)
substᶜᵗ-preserves-typing {σ = σ} wfΣ hσ hσv (⊢conceal {U = U} {A = A} hU)
  with lookupᵁ-wfty0 wfΣ hU
... | wfAt0 hA0 =
  Eq.subst
    (λ T → _ ∣ _ ⊢ U ⁻ ⦂ T ⇨ `U U)
    (Eq.sym (substᵗ-id-closed {σ = σ} hA0))
    (⊢conceal hU)
substᶜᵗ-preserves-typing {σ = σ} wfΣ hσ hσv (⊢reveal {U = U} {A = A} hU)
  with lookupᵁ-wfty0 wfΣ hU
... | wfAt0 hA0 =
  Eq.subst
    (λ T → _ ∣ _ ⊢ U ⁺ ⦂ `U U ⇨ T)
    (Eq.sym (substᵗ-id-closed {σ = σ} hA0))
    (⊢reveal hU)
substᶜᵗ-preserves-typing {Σ = Σ} {Δ = Δ} {Δ' = Δ'} {σ = σ} wfΣ hσ hσv
  (⊢∀ᶜ {A = A} {B = B} {c = c} cwt) =
  ⊢∀ᶜ
    (substᶜᵗ-preserves-typing
      {σ = extsᵗ σ}
      (rename-suc-WfStore-top wfΣ)
      (TySubstWf-exts hσ)
      (λ {X} → TySubstIsVar-exts {σ = σ} hσv {X})
      cwt)
substᶜᵗ-preserves-typing wfΣ hσ hσv (⊢⊥ hA hB) =
  ⊢⊥
    (substᵗ-preserves-WfTy hA hσ)
    (substᵗ-preserves-WfTy hB hσ)
