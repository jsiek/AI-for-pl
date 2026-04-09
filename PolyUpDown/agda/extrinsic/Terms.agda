module Terms where

-- File Charter:
--   * Extrinsic term syntax for PolyUpDown and its typing judgment.
--   * Structural actions on terms (type renaming/substitution and seal renaming),
--   * plus weakening/instantiation lemmas used by term metatheory.
--   * Terms remain independent from typing; typing/cast invariants are tracked
--   * in separate judgments.
-- Note to self:
--   * Keep operational semantics in `Reduction.agda` and term-substitution
--   * metatheory in `TermProperties.agda`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; map; []; _∷_)
open import Data.Nat using (ℕ; _+_; _<_; zero; suc; z<s; s<s)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (cong; cong₂; subst; sym; trans)

open import Types
open import TypeProperties
open import Ctx
  using
    ( ⤊ᵗ
    ; renameLookup
    ; substLookup
    ; map-substᵗ-⤊ᵗ
    ; map-substᵗ-⤊ˢ
    ; map-renameᵗ-⤊ᵗ
    ; map-renameᵗ-⤊ˢ
    ; map-renameˢ-⤊ᵗ
    ; map-renameˢ-⤊ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-ctx )
open import Store
  using
    ( _⊆ˢ_
    ; ⊆ˢ-refl
    ; done
    ; keep
    ; drop
    ; wkLookupˢ
    ; ν-⊆ˢ
    ; substStoreᵗ
    ; renameStoreᵗ-ext-⟰ᵗ
    ; substStoreᵗ-ext-⟰ᵗ
    ; renameStoreˢ-ext-⟰ᵗ
    ; renameStoreᵗ-cons-⟰ˢ
    ; substStoreᵗ-cons-⟰ˢ
    ; renameStoreˢ-cons-⟰ˢ
    )
  renaming
    ( renameLookupᵗ to renameLookupᵗ-store
    ; substLookupᵗ to substLookupᵗ-store
    )
open import UpDown

------------------------------------------------------------------------
-- Constants, primitive operators, and permission environments
------------------------------------------------------------------------

data Const : Set where
  κℕ : ℕ → Const

constTy : Const → Ty
constTy (κℕ n) = ‵ `ℕ

data Prim : Set where
  addℕ : Prim

primTy : Prim → Ty
primTy addℕ = ‵ `ℕ ⇒ ‵ `ℕ ⇒ ‵ `ℕ

data δ : Prim → Const → Const → Const → Set where
  δ-add : {m n : ℕ} →
          δ addℕ (κℕ m) (κℕ n) (κℕ (m + n))

every : SealCtx → List Bool
every zero = []
every (suc Ψ) = true ∷ every Ψ

none : SealCtx → List Bool
none zero = []
none (suc Ψ) = false ∷ none Ψ

every-member : ∀ {Ψ} (α : Seal) → α < Ψ → α ∈ every Ψ
every-member {zero} α ()
every-member {suc Ψ} zero z<s = here
every-member {suc Ψ} (suc α) (s<s α<Ψ) = there (every-member α α<Ψ)

every-index : ∀ {Ψ} {α : Seal} → α ∈ every Ψ → α < Ψ
every-index {suc Ψ} {zero} here = z<s
every-index {suc Ψ} {suc α} (there p) = s<s (every-index p)

none-excluded : ∀ {Ψ} (α : Seal) → α ∉ none Ψ
none-excluded {zero} α ()
none-excluded {suc Ψ} zero ()
none-excluded {suc Ψ} (suc α) (there p) = none-excluded α p

RenOk-every :
  ∀ {Ψ Ψ′} {ρ : Renameˢ} →
  SealRenameWf Ψ Ψ′ ρ →
  RenOk ρ (every Ψ) (every Ψ′)
RenOk-every hρ p = every-member _ (hρ (every-index p))

RenOk-none :
  ∀ {Ψ Ψ′} →
  (ρ : Renameˢ) →
  RenOk ρ (none Ψ) (none Ψ′)
RenOk-none ρ {α} p = ⊥-elim (none-excluded α p)

RenOk-any-every :
  ∀ {Ψ′} {P : List Bool} →
  (ρ : Renameˢ) →
  RenOk ρ P (every Ψ′) →
  RenOk ρ P (every Ψ′)
RenOk-any-every ρ ok = ok

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _•_
infixl 7 _up_
infixl 7 _down_
infix  5 ν:=_∙_
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_⇒_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _•_     : Term → Seal → Term
  ν:=_∙_  : Ty → Term → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _up_    : Term → Up → Term
  _down_  : Term → Down → Term
  blame   : Label → Term

------------------------------------------------------------------------
-- Well-typed casts and terms
------------------------------------------------------------------------

Wt⊑ : Store → List Bool → List Bool → Ty → Ty → Set
Wt⊑ Σ Φ Ξ A B = Σ[ p ∈ Up ] (Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B)

Wt⊒ : Store → List Bool → List Bool → Ty → Ty → Set
Wt⊒ Σ Φ Ξ A B = Σ[ p ∈ Down ] (Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B)

infix  4 _∣_∣_∣_⊢_⦂_

data _∣_∣_∣_⊢_⦂_
  (Δ : TyCtx) (Ψ : SealCtx) (Σ : Store) (Γ : Ctx)
  : Term → Ty → Set where

  ⊢` : ∀ {x A}
     → Γ ∋ x ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {M A B}
     → WfTy Δ Ψ A
     → Δ ∣ Ψ ∣ Σ ∣ (A ∷ Γ) ⊢ M ⦂ B
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (ƛ A ⇒ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {L M A B}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ (A ⇒ B)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {M A}
     → (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M A C α}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (`∀ A)
     → α ∈ every Ψ
     → Σ ∋ˢ α ⦂ C
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M • α) ⦂ A [ ｀ α ]ᵗ

  ⊢ν : ∀ {M A B}
     → WfTy Δ Ψ A
     → Δ ∣ (suc Ψ) ∣ ((zero , ⇑ˢ A) ∷ ⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ M ⦂ (⇑ˢ B)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (ν:= A ∙ M) ⦂ B

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢up : ∀ {M A B} {p : Up}
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Σ ∣ every Ψ ∣ every Ψ ⊢ p ⦂ A ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M up p) ⦂ B

  ⊢down : ∀ {M A B} {p : Down}
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Σ ∣ every Ψ ∣ every Ψ ⊢ p ⦂ A ⊒ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M down p) ⦂ B

  ⊢blame : ∀ {A}
      → (ℓ : Label)
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (blame ℓ) ⦂ A

------------------------------------------------------------------------
-- Transport helper for term typing
------------------------------------------------------------------------

cong-⊢⦂ :
  ∀ {Δ Ψ : ℕ}{Σ Σ′ : Store}{Γ Γ′ : Ctx}
    {M M′ : Term}{A A′ : Ty} →
  Σ ≡ Σ′ →
  Γ ≡ Γ′ →
  M ≡ M′ →
  A ≡ A′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ′ ⊢ M′ ⦂ A′
cong-⊢⦂ refl refl refl refl M = M


------------------------------------------------------------------------
-- Substitution of terms into terms
------------------------------------------------------------------------

renameᵗᵐ : Renameᵗ → Term → Term
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ A ⇒ M) = ƛ (renameᵗ ρ A) ⇒ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (extᵗ ρ) M)
renameᵗᵐ ρ (M • α) = renameᵗᵐ ρ M • α
renameᵗᵐ ρ (ν:= A ∙ M) = ν:= (renameᵗ ρ A) ∙ (renameᵗᵐ ρ M)
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) = renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M up p) = renameᵗᵐ ρ M up rename⊑ᵗ ρ p
renameᵗᵐ ρ (M down p) = renameᵗᵐ ρ M down rename⊒ᵗ ρ p
renameᵗᵐ ρ (blame ℓ) = blame ℓ

substᵗᵐ : Substᵗ → Term → Term
substᵗᵐ σ (` x) = ` x
substᵗᵐ σ (ƛ A ⇒ M) = ƛ (substᵗ σ A) ⇒ substᵗᵐ σ M
substᵗᵐ σ (L · M) = substᵗᵐ σ L · substᵗᵐ σ M
substᵗᵐ σ (Λ M) = Λ (substᵗᵐ (extsᵗ σ) M)
substᵗᵐ σ (M • α) = substᵗᵐ σ M • α
substᵗᵐ σ (ν:= A ∙ M) = ν:= (substᵗ σ A) ∙ (substᵗᵐ (liftSubstˢ σ) M)
substᵗᵐ σ ($ κ) = $ κ
substᵗᵐ σ (L ⊕[ op ] M) = substᵗᵐ σ L ⊕[ op ] substᵗᵐ σ M
substᵗᵐ σ (M up p) = substᵗᵐ σ M up subst⊑ᵗ σ p
substᵗᵐ σ (M down p) = substᵗᵐ σ M down subst⊒ᵗ σ p
substᵗᵐ σ (blame ℓ) = blame ℓ

renameˢᵐ : Renameˢ → Term → Term
renameˢᵐ ρ (` x) = ` x
renameˢᵐ ρ (ƛ A ⇒ M) = ƛ (renameˢ ρ A) ⇒ renameˢᵐ ρ M
renameˢᵐ ρ (L · M) = renameˢᵐ ρ L · renameˢᵐ ρ M
renameˢᵐ ρ (Λ M) = Λ (renameˢᵐ ρ M)
renameˢᵐ ρ (M • α) = renameˢᵐ ρ M • (ρ α)
renameˢᵐ ρ (ν:= A ∙ M) = ν:= (renameˢ ρ A) ∙ (renameˢᵐ (extˢ ρ) M)
renameˢᵐ ρ ($ κ) = $ κ
renameˢᵐ ρ (L ⊕[ op ] M) = renameˢᵐ ρ L ⊕[ op ] renameˢᵐ ρ M
renameˢᵐ ρ (M up p) = renameˢᵐ ρ M up rename⊑ˢ ρ p
renameˢᵐ ρ (M down p) = renameˢᵐ ρ M down rename⊒ˢ ρ p
renameˢᵐ ρ (blame ℓ) = blame ℓ

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → Ty → Term
M [ A ]ᵀ = substᵗᵐ (singleTyEnv A) M

⇑ˢᵐ : Term → Term
⇑ˢᵐ = renameˢᵐ suc

------------------------------------------------------------------------
-- Instantiation shorthand for coercions over every/every permissions
------------------------------------------------------------------------

instVarExt⊑ :
  (σ τ : Substᵗ) →
  ((X : TyVar) → Up) →
  (X : TyVar) →
  Up
instVarExt⊑ σ τ var⊑ zero = id
instVarExt⊑ σ τ var⊑ (suc X) = rename⊑ᵗ suc (var⊑ X)

instVarExt⊒ :
  (σ τ : Substᵗ) →
  ((X : TyVar) → Down) →
  (X : TyVar) →
  Down
instVarExt⊒ σ τ var⊒ zero = id
instVarExt⊒ σ τ var⊒ (suc X) = rename⊒ᵗ suc (var⊒ X)

mutual
  substᵗ-⊑ :
    (σ τ : Substᵗ) →
    ((X : TyVar) → Up) →
    ((X : TyVar) → Down) →
    (A : Ty) →
    Up
  substᵗ-⊑ σ τ var⊑ var⊒ (＇ X) = var⊑ X
  substᵗ-⊑ σ τ var⊑ var⊒ (｀ α) = id
  substᵗ-⊑ σ τ var⊑ var⊒ (‵ ι) = id
  substᵗ-⊑ σ τ var⊑ var⊒ ★ = id
  substᵗ-⊑ σ τ var⊑ var⊒ (A ⇒ B) =
    substᵗ-⊒ σ τ var⊑ var⊒ A ↦ substᵗ-⊑ σ τ var⊑ var⊒ B
  substᵗ-⊑ σ τ var⊑ var⊒ (`∀ A) =
    ∀ᵖ (substᵗ-⊑
      (extsᵗ σ)
      (extsᵗ τ)
      (instVarExt⊑ σ τ var⊑)
      (instVarExt⊒ σ τ var⊒)
      A)

  substᵗ-⊒ :
    (σ τ : Substᵗ) →
    ((X : TyVar) → Up) →
    ((X : TyVar) → Down) →
    (A : Ty) →
    Down
  substᵗ-⊒ σ τ var⊑ var⊒ (＇ X) = var⊒ X
  substᵗ-⊒ σ τ var⊑ var⊒ (｀ α) = id
  substᵗ-⊒ σ τ var⊑ var⊒ (‵ ι) = id
  substᵗ-⊒ σ τ var⊑ var⊒ ★ = id
  substᵗ-⊒ σ τ var⊑ var⊒ (A ⇒ B) =
    substᵗ-⊑ σ τ var⊑ var⊒ A ↦ substᵗ-⊒ σ τ var⊑ var⊒ B
  substᵗ-⊒ σ τ var⊑ var⊒ (`∀ A) =
    ∀ᵖ (substᵗ-⊒
      (extsᵗ σ)
      (extsᵗ τ)
      (instVarExt⊑ σ τ var⊑)
      (instVarExt⊒ σ τ var⊒)
      A)

mutual
  instSubst⊑-wt :
    ∀ {Ψ}{Σ : Store} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    ((X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊑ X ⦂ σ X ⊑ τ X) →
    ((X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊒ X ⦂ τ X ⊒ σ X) →
    (A : Ty) →
    Σ ∣ every Ψ ∣ every Ψ ⊢ substᵗ-⊑ σ τ var⊑ var⊒ A ⦂ substᵗ σ A ⊑ substᵗ τ A
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (＇ X) = h⊑ X
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (｀ α) = wt-id
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (‵ ι) = wt-id
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ ★ = wt-id
  instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ (A ⇒ B) =
    wt-↦
      (instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ A)
      (instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ B)
  instSubst⊑-wt {Ψ = Ψ} {Σ = Σ} σ τ var⊑ var⊒ h⊑ h⊒ (`∀ A) =
    wt-∀
      (instSubst⊑-wt
        (extsᵗ σ)
        (extsᵗ τ)
        (instVarExt⊑ σ τ var⊑)
        (instVarExt⊒ σ τ var⊒)
        h⊑′
        h⊒′
        A)
      where
      h⊑′ : (X : TyVar) →
        ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ instVarExt⊑ σ τ var⊑ X ⦂ extsᵗ σ X ⊑ extsᵗ τ X
      h⊑′ zero = wt-id
      h⊑′ (suc X) = ⊑-renameᵗ-wt suc (h⊑ X)

      h⊒′ : (X : TyVar) →
        ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ instVarExt⊒ σ τ var⊒ X ⦂ extsᵗ τ X ⊒ extsᵗ σ X
      h⊒′ zero = wt-id
      h⊒′ (suc X) = ⊒-renameᵗ-wt suc (h⊒ X)

  instSubst⊒-wt :
    ∀ {Ψ}{Σ : Store} →
    (σ τ : Substᵗ) →
    (var⊑ : (X : TyVar) → Up) →
    (var⊒ : (X : TyVar) → Down) →
    ((X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊑ X ⦂ σ X ⊑ τ X) →
    ((X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊒ X ⦂ τ X ⊒ σ X) →
    (A : Ty) →
    Σ ∣ every Ψ ∣ every Ψ ⊢ substᵗ-⊒ σ τ var⊑ var⊒ A ⦂ substᵗ τ A ⊒ substᵗ σ A
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (＇ X) = h⊒ X
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (｀ α) = wt-id
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (‵ ι) = wt-id
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ ★ = wt-id
  instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ (A ⇒ B) =
    wt-↦
      (instSubst⊑-wt σ τ var⊑ var⊒ h⊑ h⊒ A)
      (instSubst⊒-wt σ τ var⊑ var⊒ h⊑ h⊒ B)
  instSubst⊒-wt {Ψ = Ψ} {Σ = Σ} σ τ var⊑ var⊒ h⊑ h⊒ (`∀ A) =
    wt-∀
      (instSubst⊒-wt
        (extsᵗ σ)
        (extsᵗ τ)
        (instVarExt⊑ σ τ var⊑)
        (instVarExt⊒ σ τ var⊒)
        h⊑′
        h⊒′
        A)
      where
      h⊑′ : (X : TyVar) →
        ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ instVarExt⊑ σ τ var⊑ X ⦂ extsᵗ σ X ⊑ extsᵗ τ X
      h⊑′ zero = wt-id
      h⊑′ (suc X) = ⊑-renameᵗ-wt suc (h⊑ X)

      h⊒′ : (X : TyVar) →
        ⟰ᵗ Σ ∣ every Ψ ∣ every Ψ ⊢ instVarExt⊒ σ τ var⊒ X ⦂ extsᵗ τ X ⊒ extsᵗ σ X
      h⊒′ zero = wt-id
      h⊒′ (suc X) = ⊒-renameᵗ-wt suc (h⊒ X)

instSubst⊒ :
  ∀ {Ψ}{Σ : Store} →
  (σ τ : Substᵗ) →
  ((X : TyVar) → Wt⊑ Σ (every Ψ) (every Ψ) (σ X) (τ X)) →
  ((X : TyVar) → Wt⊒ Σ (every Ψ) (every Ψ) (τ X) (σ X)) →
  (A : Ty) →
  Wt⊒ Σ (every Ψ) (every Ψ) (substᵗ τ A) (substᵗ σ A)
instSubst⊒ {Ψ = Ψ} {Σ = Σ} σ τ var⊑ var⊒ A = p , hp
  where
    var⊑r : (X : TyVar) → Up
    var⊑r X = proj₁ (var⊑ X)

    var⊒r : (X : TyVar) → Down
    var⊒r X = proj₁ (var⊒ X)

    var⊑-wt : (X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊑r X ⦂ σ X ⊑ τ X
    var⊑-wt X = proj₂ (var⊑ X)

    var⊒-wt : (X : TyVar) → Σ ∣ every Ψ ∣ every Ψ ⊢ var⊒r X ⦂ τ X ⊒ σ X
    var⊒-wt X = proj₂ (var⊒ X)

    p : Down
    p = substᵗ-⊒ σ τ var⊑r var⊒r A

    hp : Σ ∣ every Ψ ∣ every Ψ ⊢ p ⦂ substᵗ τ A ⊒ substᵗ σ A
    hp = instSubst⊒-wt σ τ var⊑r var⊒r var⊑-wt var⊒-wt A

instVar⊑ :
  (A : Ty) →
  (α : Seal) →
  (X : TyVar) →
  Up
instVar⊑ A α zero = unseal α
instVar⊑ A α (suc X) = id

instVar⊑-wt :
  ∀ {Ψ}{Σ : Store}{A : Ty}{α : Seal} →
  (h : Σ ∋ˢ α ⦂ A) →
  (α∈ : α ∈ every Ψ) →
  (X : TyVar) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ instVar⊑ A α X ⦂ singleTyEnv (｀ α) X ⊑ singleTyEnv A X
instVar⊑-wt h α∈ zero = wt-unseal h α∈
instVar⊑-wt h α∈ (suc X) = wt-id

instVar⊒ :
  (A : Ty) →
  (α : Seal) →
  (X : TyVar) →
  Down
instVar⊒ A α zero = seal α
instVar⊒ A α (suc X) = id

instVar⊒-wt : ∀ {Ψ}{Σ : Store}{A : Ty}{α : Seal} →
  (h : Σ ∋ˢ α ⦂ A) (α∈ : α ∈ every Ψ) (X : TyVar) →
  Σ ∣ every Ψ ∣ every Ψ ⊢ instVar⊒ A α X ⦂ singleTyEnv A X ⊒ singleTyEnv (｀ α) X
instVar⊒-wt h α∈ zero = wt-seal h α∈
instVar⊒-wt h α∈ (suc X) = wt-id

instCast⊑ : ∀ {A : Ty}{B : Ty}{α : Seal} →
  Up
instCast⊑ {A = A} {B = B} {α = α} =
  substᵗ-⊑ (singleTyEnv (｀ α)) (singleTyEnv A) (instVar⊑ A α) (instVar⊒ A α) B

instCast⊑-wt : ∀ {Ψ}{Σ : Store}{A : Ty}{B : Ty}{α : Seal} →
  (h : Σ ∋ˢ α ⦂ A) →
  α ∈ every Ψ →
  Σ ∣ every Ψ ∣ every Ψ ⊢ instCast⊑ {A = A} {B = B} {α = α} ⦂ (B [ ｀ α ]ᵗ) ⊑ (B [ A ]ᵗ)
instCast⊑-wt {A = A} {B = B} {α = α} h α∈ =
  instSubst⊑-wt (singleTyEnv (｀ α)) (singleTyEnv A) (instVar⊑ A α)
    (instVar⊒ A α) (instVar⊑-wt h α∈) (instVar⊒-wt h α∈) B

instCast⊒ :
  ∀ {A : Ty}{B : Ty}{α : Seal} →
  Down
instCast⊒ {A = A} {B = B} {α = α} =
  substᵗ-⊒
    (singleTyEnv (｀ α))
    (singleTyEnv A)
    (instVar⊑ A α)
    (instVar⊒ A α)
    B

instCast⊒-wt :
  ∀ {Ψ}{Σ : Store}{A : Ty}{B : Ty}{α : Seal} →
  (h : Σ ∋ˢ α ⦂ A) →
  α ∈ every Ψ →
  Σ ∣ every Ψ ∣ every Ψ ⊢ instCast⊒ {A = A} {B = B} {α = α} ⦂ (B [ A ]ᵗ) ⊒ (B [ ｀ α ]ᵗ)
instCast⊒-wt {A = A} {B = B} {α = α} h α∈ =
  instSubst⊒-wt (singleTyEnv (｀ α)) (singleTyEnv A) (instVar⊑ A α)
    (instVar⊒ A α) (instVar⊑-wt h α∈) (instVar⊒-wt h α∈) B

------------------------------------------------------------------------
-- Store weakening for casts and terms
------------------------------------------------------------------------

inst-⟰ᵗ-⊆ˢ :
  ∀ {Σ Σ′ : Store} →
  Σ ⊆ˢ Σ′ →
  ⟰ᵗ Σ ⊆ˢ ⟰ᵗ Σ′
inst-⟰ᵗ-⊆ˢ done = done
inst-⟰ᵗ-⊆ˢ (keep {α = α} {A = A} w) =
  keep {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)
inst-⟰ᵗ-⊆ˢ (drop {α = α} {A = A} w) =
  drop {α = α} {A = renameᵗ suc A} (inst-⟰ᵗ-⊆ˢ w)

mutual
  wk⊑ : ∀ {Σ Σ′ : Store}{Φ Ξ : List Bool}{A B : Ty}{p : Up} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B →
    Σ′ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊑ B
  wk⊑ w (wt-tag g gok) = wt-tag g gok
  wk⊑ w (wt-unseal h α∈Φ) = wt-unseal (wkLookupˢ w h) α∈Φ
  wk⊑ w (wt-↦ p q) = wt-↦ (wk⊒ w p) (wk⊑ w q)
  wk⊑ w (wt-∀ p) = wt-∀ (wk⊑ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊑ w (wt-ν p) = wt-ν (wk⊑ (ν-⊆ˢ ★ w) p)
  wk⊑ w wt-id = wt-id
  wk⊑ w (wt-； p q) = wt-； (wk⊑ w p) (wk⊑ w q)

  wk⊒ : ∀ {Σ Σ′ : Store}{Φ Ξ : List Bool}{A B : Ty}{p : Down} →
    Σ ⊆ˢ Σ′ →
    Σ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B →
    Σ′ ∣ Φ ∣ Ξ ⊢ p ⦂ A ⊒ B
  wk⊒ w (wt-untag g gok ℓ) = wt-untag g gok ℓ
  wk⊒ w (wt-seal h α∈Φ) = wt-seal (wkLookupˢ w h) α∈Φ
  wk⊒ w (wt-↦ p q) = wt-↦ (wk⊑ w p) (wk⊒ w q)
  wk⊒ w (wt-∀ p) = wt-∀ (wk⊒ (inst-⟰ᵗ-⊆ˢ w) p)
  wk⊒ w (wt-ν p) = wt-ν (wk⊒ (ν-⊆ˢ ★ w) p)
  wk⊒ w wt-id = wt-id
  wk⊒ w (wt-； p q) = wt-； (wk⊒ w p) (wk⊒ w q)

wkΣ-term : ∀ {Δ Ψ}{Σ Σ′ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Σ ⊆ˢ Σ′ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ ∣ Σ′ ∣ Γ ⊢ M ⦂ A
wkΣ-term w (⊢` h) = ⊢` h
wkΣ-term w (⊢ƛ wfA M) = ⊢ƛ wfA (wkΣ-term w M)
wkΣ-term w (⊢· L M) = ⊢· (wkΣ-term w L) (wkΣ-term w M)
wkΣ-term w (⊢Λ M) = ⊢Λ (wkΣ-term (inst-⟰ᵗ-⊆ˢ w) M)
wkΣ-term w (⊢• M α∈ h) = ⊢• (wkΣ-term w M) α∈ (wkLookupˢ w h)
wkΣ-term w (⊢ν {A = A} wfA M) = ⊢ν wfA (wkΣ-term (ν-⊆ˢ A w) M)
wkΣ-term w (⊢$ κ) = ⊢$ κ
wkΣ-term w (⊢⊕ L op M) = ⊢⊕ (wkΣ-term w L) op (wkΣ-term w M)
wkΣ-term w (⊢up M⊢ hp) = ⊢up (wkΣ-term w M⊢) (wk⊑ w hp)
wkΣ-term w (⊢down M⊢ hp) = ⊢down (wkΣ-term w M⊢) (wk⊒ w hp)
wkΣ-term w (⊢blame ℓ) = ⊢blame ℓ

------------------------------------------------------------------------
-- Auxiliary lookup and instantiation lemmas
------------------------------------------------------------------------

reveal-⊑ : (A : Ty) (B : Ty) →
  Up
reveal-⊑ A B =
  substᵗ-⊑
    (singleTyEnv (｀ zero))
    (singleTyEnv (⇑ˢ A))
    (instVar⊑ (⇑ˢ A) zero)
    (instVar⊒ (⇑ˢ A) zero)
    (⇑ˢ B)

inst-⇑ˢ : ∀ (A : Ty) (B : Ty) →
  (⇑ˢ B) [ ⇑ˢ A ]ᵗ ≡ ⇑ˢ (B [ A ]ᵗ)
inst-⇑ˢ A B =
  trans
    (substᵗ-cong env (⇑ˢ B))
    (substᵗ-⇑ˢ (singleTyEnv A) B)
  where
    env : (X : TyVar) →
      singleTyEnv (⇑ˢ A) X ≡ liftSubstˢ (singleTyEnv A) X
    env zero = refl
    env (suc X) = refl

------------------------------------------------------------------------
-- Structural actions preserve typing
------------------------------------------------------------------------

renameᵗ-constTy : (ρ : Renameᵗ) (κ : Const) →
  renameᵗ ρ (constTy κ) ≡ constTy κ
renameᵗ-constTy ρ (κℕ n) = refl

substᵗ-constTy : (σ : Substᵗ) (κ : Const) →
  substᵗ σ (constTy κ) ≡ constTy κ
substᵗ-constTy σ (κℕ n) = refl

renameˢ-constTy : (ρ : Renameˢ) (κ : Const) →
  renameˢ ρ (constTy κ) ≡ constTy κ
renameˢ-constTy ρ (κℕ n) = refl

renameᵗ-term : ∀ {Δ Δ′ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} (ρ : Renameᵗ) →
  TyRenameWf Δ Δ′ ρ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Ψ ∣ renameStoreᵗ ρ Σ ∣ map (renameᵗ ρ) Γ ⊢ renameᵗᵐ ρ M ⦂ renameᵗ ρ A
renameᵗ-term ρ hρ (⊢` h) = ⊢` (renameLookupᵗ-ctx ρ h)
renameᵗ-term ρ hρ (⊢ƛ wfA M) =
  ⊢ƛ (renameᵗ-preserves-WfTy wfA hρ) (renameᵗ-term ρ hρ M)
renameᵗ-term ρ hρ (⊢· L M) = ⊢· (renameᵗ-term ρ hρ L) (renameᵗ-term ρ hρ M)
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ hρ (⊢Λ {A = A} M) =
  ⊢Λ
    (cong-⊢⦂
      (renameStoreᵗ-ext-⟰ᵗ ρ Σ)
      (map-renameᵗ-⤊ᵗ ρ Γ)
      refl
      refl
      (renameᵗ-term (extᵗ ρ) (TyRenameWf-ext hρ) M))
renameᵗ-term ρ hρ (⊢• {A = A} {α = α} M α∈ h) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameᵗ-[]ᵗ-seal ρ A α))
    (⊢• (renameᵗ-term ρ hρ M) α∈ (renameLookupᵗ-store ρ h))
renameᵗ-term {Σ = Σ} {Γ = Γ} ρ hρ (⊢ν {A = A} {B = B} wfA M) =
  ⊢ν
    (renameᵗ-preserves-WfTy wfA hρ)
    (cong-⊢⦂
      (renameStoreᵗ-cons-⟰ˢ ρ A Σ)
      (map-renameᵗ-⤊ˢ ρ Γ)
      refl
      (renameᵗ-⇑ˢ ρ B)
      (renameᵗ-term ρ hρ M))
renameᵗ-term ρ hρ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (renameᵗ-constTy ρ κ)) (⊢$ κ)
renameᵗ-term ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameᵗ-term ρ hρ L) op (renameᵗ-term ρ hρ M)
renameᵗ-term ρ hρ (⊢up {p = p} M⊢ hp) =
  ⊢up {p = rename⊑ᵗ ρ p}
    (renameᵗ-term ρ hρ M⊢)
    (⊑-renameᵗ-wt ρ hp)
renameᵗ-term ρ hρ (⊢down {p = p} M⊢ hp) =
  ⊢down {p = rename⊒ᵗ ρ p}
    (renameᵗ-term ρ hρ M⊢)
    (⊒-renameᵗ-wt ρ hp)
renameᵗ-term ρ hρ (⊢blame ℓ) = ⊢blame ℓ

substᵗ-wt :
  ∀ {Δ Δ′ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (σ : Substᵗ) →
  TySubstWf Δ Δ′ Ψ σ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ′ ∣ Ψ ∣ substStoreᵗ σ Σ ∣ map (substᵗ σ) Γ ⊢ substᵗᵐ σ M ⦂ substᵗ σ A
substᵗ-wt σ hσ (⊢` h) = ⊢` (substLookup σ h)
substᵗ-wt σ hσ (⊢ƛ wfA M) =
  ⊢ƛ (substᵗ-preserves-WfTy wfA hσ) (substᵗ-wt σ hσ M)
substᵗ-wt σ hσ (⊢· L M) = ⊢· (substᵗ-wt σ hσ L) (substᵗ-wt σ hσ M)
substᵗ-wt {Σ = Σ} {Γ = Γ} σ hσ (⊢Λ {A = A} M) =
  ⊢Λ
    (cong-⊢⦂
      (substStoreᵗ-ext-⟰ᵗ σ Σ)
      (map-substᵗ-⤊ᵗ σ Γ)
      refl
      refl
      (substᵗ-wt (extsᵗ σ) (TySubstWf-exts hσ) M))
substᵗ-wt σ hσ (⊢• {A = A} {α = α} M α∈ h) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (substᵗ-[]ᵗ-seal σ A α))
    (⊢• (substᵗ-wt σ hσ M) α∈ (substLookupᵗ-store σ h))
substᵗ-wt {Σ = Σ} {Γ = Γ} σ hσ (⊢ν {A = A} {B = B} wfA M) =
  ⊢ν
    (substᵗ-preserves-WfTy wfA hσ)
    (cong-⊢⦂
      (substStoreᵗ-cons-⟰ˢ σ A Σ)
      (map-substᵗ-⤊ˢ σ Γ)
      refl
      (substᵗ-⇑ˢ σ B)
      (substᵗ-wt (liftSubstˢ σ) (TySubstWf-liftˢ hσ) M))
substᵗ-wt σ hσ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (substᵗ-constTy σ κ)) (⊢$ κ)
substᵗ-wt σ hσ (⊢⊕ L op M) =
  ⊢⊕ (substᵗ-wt σ hσ L) op (substᵗ-wt σ hσ M)
substᵗ-wt σ hσ (⊢up {p = p} M⊢ hp) =
  ⊢up {p = subst⊑ᵗ σ p}
    (substᵗ-wt σ hσ M⊢)
    (⊑-substᵗ-wt σ hp)
substᵗ-wt σ hσ (⊢down {p = p} M⊢ hp) =
  ⊢down {p = subst⊒ᵗ σ p}
    (substᵗ-wt σ hσ M⊢)
    (⊒-substᵗ-wt σ hp)
substᵗ-wt σ hσ (⊢blame ℓ) = ⊢blame ℓ

renameˢ-wt :
  ∀ {Δ Ψ Ψ′}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  (ρ : Renameˢ) →
  SealRenameWf Ψ Ψ′ ρ →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ Ψ′ ∣ renameStoreˢ ρ Σ ∣ map (renameˢ ρ) Γ ⊢ renameˢᵐ ρ M ⦂ renameˢ ρ A
renameˢ-wt ρ hρ (⊢` h) = ⊢` (renameLookup ρ h)
renameˢ-wt ρ hρ (⊢ƛ wfA M) =
  ⊢ƛ (renameˢ-preserves-WfTy wfA hρ) (renameˢ-wt ρ hρ M)
renameˢ-wt ρ hρ (⊢· L M) = ⊢· (renameˢ-wt ρ hρ L) (renameˢ-wt ρ hρ M)
renameˢ-wt {Σ = Σ} {Γ = Γ} ρ hρ (⊢Λ {A = A} M) =
  ⊢Λ
    (cong-⊢⦂
      (renameStoreˢ-ext-⟰ᵗ ρ Σ)
      (map-renameˢ-⤊ᵗ ρ Γ)
      refl
      refl
      (renameˢ-wt ρ hρ M))
renameˢ-wt {Ψ = Ψ} ρ hρ (⊢• {A = A} {α = α} M α∈ h) =
  cong-⊢⦂
    refl
    refl
    refl
    (sym (renameˢ-[]ᵗ-seal ρ A α))
    (⊢•
      (renameˢ-wt ρ hρ M)
      (RenOk-every hρ α∈)
      (renameLookupˢ ρ h))
renameˢ-wt {Σ = Σ} {Γ = Γ} ρ hρ (⊢ν {A = A} {B = B} wfA M) =
  ⊢ν
    (renameˢ-preserves-WfTy wfA hρ)
    (cong-⊢⦂
      (renameStoreˢ-cons-⟰ˢ ρ A Σ)
      (map-renameˢ-⤊ˢ ρ Γ)
      refl
      (renameˢ-ext-⇑ˢ ρ B)
      (renameˢ-wt (extˢ ρ) (SealRenameWf-ext hρ) M))
renameˢ-wt ρ hρ (⊢$ κ) =
  cong-⊢⦂ refl refl refl (sym (renameˢ-constTy ρ κ)) (⊢$ κ)
renameˢ-wt ρ hρ (⊢⊕ L op M) =
  ⊢⊕ (renameˢ-wt ρ hρ L) op (renameˢ-wt ρ hρ M)
renameˢ-wt ρ hρ (⊢up {p = p} M⊢ hp) =
  ⊢up {p = rename⊑ˢ ρ p}
    (renameˢ-wt ρ hρ M⊢)
    (⊑-renameˢ-wt ρ (RenOk-every hρ) (RenOk-every hρ) hp)
renameˢ-wt ρ hρ (⊢down {p = p} M⊢ hp) =
  ⊢down {p = rename⊒ˢ ρ p}
    (renameˢ-wt ρ hρ M⊢)
    (⊒-renameˢ-wt ρ (RenOk-every hρ) (RenOk-every hρ) hp)
renameˢ-wt ρ hρ (⊢blame ℓ) = ⊢blame ℓ

⇑ˢᵐ-wt : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx}{M : Term}{A : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A →
  Δ ∣ (suc Ψ) ∣ (⟰ˢ Σ) ∣ (⤊ˢ Γ) ⊢ ⇑ˢᵐ M ⦂ ⇑ˢ A
⇑ˢᵐ-wt M = renameˢ-wt suc SealRenameWf-suc M

------------------------------------------------------------------------
-- Instantiation helper for terms
------------------------------------------------------------------------

inst : ∀ {Δ Ψ}{Σ : Store}{Γ : Ctx} {L : Term}{A B : Ty} →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ `∀ B →
  WfTy Δ Ψ A →
  Δ ∣ Ψ ∣ Σ ∣ Γ ⊢
    (ν:= A ∙ ((⇑ˢᵐ L • zero) up (reveal-⊑ A B)))
    ⦂ B [ A ]ᵗ
inst {Ψ = Ψ} {Σ = Σ} {A = A} {B = B} L wfA =
  ⊢ν wfA (cong-⊢⦂ refl refl refl (inst-⇑ˢ A B)
         (⊢up
           (⊢• (wkΣ-term (drop ⊆ˢ-refl) (⇑ˢᵐ-wt L)) here (Z∋ˢ refl refl))
           (instSubst⊑-wt
             (singleTyEnv (｀ zero))
             (singleTyEnv (⇑ˢ A))
             (instVar⊑ (⇑ˢ A) zero)
             (instVar⊒ (⇑ˢ A) zero)
             (instVar⊑-wt (Z∋ˢ refl refl) here)
             (instVar⊒-wt (Z∋ˢ refl refl) here)
             (⇑ˢ B))))
