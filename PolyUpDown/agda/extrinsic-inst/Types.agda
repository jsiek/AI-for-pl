module Types where

-- File Charter:
--   * Core syntax and primitive operations for extrinsic types, contexts, and stores.
--   * Definitions only (renaming/substitution/opening operators, lookup relations,
--   * and well-formedness judgments).
--   * No deep proof engineering or coercion-specific metatheory.
-- Note to self:
--   * Keep this file focused on syntax/judgments; place algebraic lemmas in
--     `TypeProperties.agda` and context/store-specific theorems in their modules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (cong)

------------------------------------------------------------------------
-- Variables, contexts, base types
------------------------------------------------------------------------

Var : Set
Var = ℕ

TyVar : Set
TyVar = Var

Seal : Set
Seal = Var

TyCtx : Set
TyCtx = ℕ

SealCtx : Set
SealCtx = ℕ

data Base : Set where
  `ℕ : Base
  `𝔹 : Base

infixr 7 _⇒_
infix 6 `∀

data Ty : Set where
  ＇_ : TyVar → Ty
  ｀_ : Seal → Ty
  ‵_ : Base → Ty
  ★ : Ty
  _⇒_ : Ty → Ty → Ty
  `∀ : Ty → Ty

data Cross : Ty → Set where
  ＇_ : (X : TyVar) → Cross (＇ X)
  ｀_ : (α : Seal) → Cross (｀ α)
  ‵_ : (ι : Base) → Cross (‵ ι)
  _⇒_ : (A : Ty) → (B : Ty) → Cross (A ⇒ B)
  `∀ : (A : Ty) → Cross (`∀ A)

data Ground : Ty → Set where
  ｀_ : (α : Seal) → Ground (｀ α)
  ‵_ : (ι : Base) → Ground (‵ ι)
  ★⇒★ : Ground (★ ⇒ ★)

infix 4 _≟Base_
_≟Base_ : (ι ι′ : Base) → Dec (ι ≡ ι′)
`ℕ ≟Base `ℕ = yes refl
`ℕ ≟Base `𝔹 = no (λ ())
`𝔹 ≟Base `ℕ = no (λ ())
`𝔹 ≟Base `𝔹 = yes refl

seal-≟ : (α β : Seal) → Dec (α ≡ β)
seal-≟ = _≟_

infix 4 _≟Ground_
_≟Ground_ :
  ∀ {G H : Ty} →
  Ground G →
  Ground H →
  Dec (G ≡ H)
(｀ α) ≟Ground (｀ β) with seal-≟ α β
... | yes eq = yes (cong ｀_ eq)
... | no neq = no (λ { refl → neq refl })
(｀ α) ≟Ground (‵ ι) = no (λ ())
(｀ α) ≟Ground ★⇒★ = no (λ ())
(‵ ι) ≟Ground (｀ α) = no (λ ())
(‵ ι) ≟Ground (‵ ι′) with ι ≟Base ι′
... | yes eq = yes (cong ‵_ eq)
... | no neq = no (λ { refl → neq refl })
(‵ ι) ≟Ground ★⇒★ = no (λ ())
★⇒★ ≟Ground (｀ α) = no (λ ())
★⇒★ ≟Ground (‵ ι) = no (λ ())
★⇒★ ≟Ground ★⇒★ = yes refl

Ctx : Set
Ctx = List Ty

Store : Set
Store = List (Seal × Ty)

∅ˢ : Store
∅ˢ = []

extendˢ : Store → Seal → Ty → Store
extendˢ Σ α A = (α , A) ∷ Σ

------------------------------------------------------------------------
-- Type-variable substitution (de Bruijn X)
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = TyVar → TyVar

Substᵗ : Set
Substᵗ = TyVar → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (＇ X) = ＇ (ρ X)
renameᵗ ρ (｀ α) = ｀ α
renameᵗ ρ (‵ ι) = ‵ ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ (renameᵗ (extᵗ ρ) A)

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero = ＇ zero
extsᵗ σ (suc X) = renameᵗ suc (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (＇ X) = σ X
substᵗ σ (｀ α) = ｀ α
substᵗ σ (‵ ι) = ‵ ι
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A) = `∀ (substᵗ (extsᵗ σ) A)

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero = B
singleTyEnv B (suc X) = ＇ X

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

renameStoreᵗ : Renameᵗ → Store → Store
renameStoreᵗ ρ [] = []
renameStoreᵗ ρ ((α , A) ∷ Σ) =
  (α , renameᵗ ρ A) ∷ renameStoreᵗ ρ Σ

⟰ᵗ : Store → Store
⟰ᵗ = renameStoreᵗ suc

------------------------------------------------------------------------
-- Seal-variable renaming/opening (for ν binders over α)
------------------------------------------------------------------------

Renameˢ : Set
Renameˢ = Seal → Seal

extˢ : Renameˢ → Renameˢ
extˢ ρ zero = zero
extˢ ρ (suc α) = suc (ρ α)

singleSealEnv : Seal → Renameˢ
singleSealEnv α zero = α
singleSealEnv α (suc α′) = α′

renameˢ : Renameˢ → Ty → Ty
renameˢ ρ (＇ X) = ＇ X
renameˢ ρ (｀ α) = ｀ (ρ α)
renameˢ ρ (‵ ι) = ‵ ι
renameˢ ρ ★ = ★
renameˢ ρ (A ⇒ B) = renameˢ ρ A ⇒ renameˢ ρ B
renameˢ ρ (`∀ A) = `∀ (renameˢ ρ A)

⇑ˢ : Ty → Ty
⇑ˢ = renameˢ suc

⤊ˢ : Ctx → Ctx
⤊ˢ Γ = map ⇑ˢ Γ

renameStoreˢ : Renameˢ → Store → Store
renameStoreˢ ρ [] = []
renameStoreˢ ρ ((α , A) ∷ Σ) =
  (ρ α , renameˢ ρ A) ∷ renameStoreˢ ρ Σ

⟰ˢ : Store → Store
⟰ˢ = renameStoreˢ suc

infixl 8 _[_]ˢ
_[_]ˢ : Ty → Seal → Ty
A [ α ]ˢ = renameˢ (singleSealEnv α) A

------------------------------------------------------------------------
-- Well-formedness and lookups
------------------------------------------------------------------------

data WfTy : TyCtx → SealCtx → Ty → Set where
  wfVar : ∀ {Δ Ψ X} → X < Δ → WfTy Δ Ψ (＇ X)
  wfSeal : ∀ {Δ Ψ α} → α < Ψ → WfTy Δ Ψ (｀ α)
  wfBase : ∀ {Δ Ψ ι} → WfTy Δ Ψ (‵ ι)
  wf★ : ∀ {Δ Ψ} → WfTy Δ Ψ ★
  wf⇒ : ∀ {Δ Ψ A B} → WfTy Δ Ψ A → WfTy Δ Ψ B → WfTy Δ Ψ (A ⇒ B)
  wf∀ : ∀ {Δ Ψ A} → WfTy (suc Δ) Ψ A → WfTy Δ Ψ (`∀ A)

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : ∀ {Γ A} →
      (A ∷ Γ) ∋ zero ⦂ A

  S : ∀ {Γ A B x} →
      Γ ∋ x ⦂ A →
      (B ∷ Γ) ∋ suc x ⦂ A

infix 4 _∋ˢ_⦂_
data _∋ˢ_⦂_ : Store → Seal → Ty → Set where
  Z∋ˢ : ∀ {Σ A B α β}
       → α ≡ β
       → A ≡ B
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A

  S∋ˢ : ∀ {Σ α β A B}
       → Σ ∋ˢ α ⦂ A
       → ((β , B) ∷ Σ) ∋ˢ α ⦂ A
