module PolyCoercions where

open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
open import Data.Bool using (Bool)

------------------------------------------------------------------------
-- Variables, Contexts, and Types
------------------------------------------------------------------------

Var : Set
Var = ℕ

Name : Set
Name = ℕ

Label : Set
Label = ℕ

TyCtx : Set
TyCtx = ℕ

infixr 7 _⇒_
infix  6 `∀

data Ty : Set where
  `_    : Var → Ty
  `ℕ    : Ty
  `Bool : Ty
  `Str  : Ty
  `★    : Ty
  `U_   : Name → Ty
  _⇒_   : Ty → Ty → Ty
  `∀    : Ty → Ty

Ctx : Set
Ctx = List Ty

Store : Set
Store = List Ty

------------------------------------------------------------------------
-- Type-level renaming and substitution
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = Var → Var

Substᵗ : Set
Substᵗ = Var → Ty

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero    = zero
extᵗ ρ (suc i) = suc (ρ i)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` i)     = ` (ρ i)
renameᵗ ρ `ℕ        = `ℕ
renameᵗ ρ `Bool     = `Bool
renameᵗ ρ `Str      = `Str
renameᵗ ρ `★        = `★
renameᵗ ρ (`U u)    = `U u
renameᵗ ρ (A ⇒ B)   = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (`∀ A)    = `∀ (renameᵗ (extᵗ ρ) A)

renameΣ : Renameᵗ → Store → Store
renameΣ ρ Σ = map (renameᵗ ρ) Σ

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero    = ` zero
extsᵗ σ (suc i) = renameᵗ suc (σ i)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (` i)    = σ i
substᵗ σ `ℕ       = `ℕ
substᵗ σ `Bool    = `Bool
substᵗ σ `Str     = `Str
substᵗ σ `★       = `★
substᵗ σ (`U u)   = `U u
substᵗ σ (A ⇒ B)  = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (`∀ A)   = `∀ (substᵗ (extsᵗ σ) A)

substΣ : Substᵗ → Store → Store
substΣ σ Σ = map (substᵗ σ) Σ

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero    = B
singleTyEnv B (suc i) = ` i

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

⤊ : Ctx → Ctx
⤊ Γ = map (renameᵗ suc) Γ

------------------------------------------------------------------------
-- Well-formedness and lookup
------------------------------------------------------------------------

infix 4 _∋_⦂_

data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z : ∀ {Γ A} → (A ∷ Γ) ∋ zero ⦂ A
  S : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (B ∷ Γ) ∋ suc x ⦂ A

infix 4 _∋ᵁ_⦂_

data _∋ᵁ_⦂_ : Store → Name → Ty → Set where
  Zᵁ : ∀ {Σ A} → (A ∷ Σ) ∋ᵁ zero ⦂ A
  Sᵁ : ∀ {Σ A B u} → Σ ∋ᵁ u ⦂ A → (B ∷ Σ) ∋ᵁ suc u ⦂ A

data WfTy : TyCtx → Store → Ty → Set where
  wfVar  : ∀ {Δ Σ X} → X < Δ → WfTy Δ Σ (` X)
  wfℕ    : ∀ {Δ Σ} → WfTy Δ Σ `ℕ
  wfBool : ∀ {Δ Σ} → WfTy Δ Σ `Bool
  wfStr  : ∀ {Δ Σ} → WfTy Δ Σ `Str
  wf★    : ∀ {Δ Σ} → WfTy Δ Σ `★
  wfU    : ∀ {Δ Σ U A} → Σ ∋ᵁ U ⦂ A → WfTy Δ Σ (`U U)
  wf⇒    : ∀ {Δ Σ A B} → WfTy Δ Σ A → WfTy Δ Σ B → WfTy Δ Σ (A ⇒ B)
  wf∀    : ∀ {Δ Σ A} → WfTy (suc Δ) (renameΣ suc Σ) A → WfTy Δ Σ (`∀ A)

data NonDyn : Ty → Set where
  ndVar  : ∀ {X} → NonDyn (` X)
  ndℕ    : NonDyn `ℕ
  ndBool : NonDyn `Bool
  ndStr  : NonDyn `Str
  ndU    : ∀ {U} → NonDyn (`U U)
  nd⇒    : ∀ {A B} → NonDyn (A ⇒ B)
  nd∀    : ∀ {A} → NonDyn (`∀ A)

data WfStore : Store → Set where
  wfΣ∅  : WfStore []
  wfΣ∷  : ∀ {Σ A}
    → WfStore Σ
    → NonDyn A
    → WfTy zero Σ A
    → WfStore (A ∷ Σ)

data WfCtx : TyCtx → Store → Ctx → Set where
  wfΓ∅  : ∀ {Δ Σ} → WfCtx Δ Σ []
  wfΓ∷  : ∀ {Δ Σ Γ A}
    → WfCtx Δ Σ Γ
    → WfTy Δ Σ A
    → WfCtx Δ Σ (A ∷ Γ)

------------------------------------------------------------------------
-- Ground types and coercions (Fig. 1)
------------------------------------------------------------------------

data Ground : Ty → Set where
  G-ℕ    : Ground `ℕ
  G-Bool : Ground `Bool
  G-Str  : Ground `Str
  G-⇒★   : Ground (`★ ⇒ `★)
  G-∀★   : Ground (`∀ `★)
  G-var  : ∀ {X} → Ground (` X)
  G-U    : ∀ {U} → Ground (`U U)

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
    → WfStore Σ
    → WfTy Δ Σ A
    → Σ ∣ Δ ⊢ idᶜ A ⦂ A ⇨ A

  ⊢! : ∀ {G}
    → WfStore Σ
    → WfTy Δ Σ G
    → Ground G
    → Σ ∣ Δ ⊢ G ! ⦂ G ⇨ `★

  ⊢? : ∀ {G p}
    → WfStore Σ
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
    → WfStore Σ
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁻ ⦂ A ⇨ `U U

  ⊢reveal : ∀ {U A}
    → WfStore Σ
    → Σ ∋ᵁ U ⦂ A
    → Σ ∣ Δ ⊢ U ⁺ ⦂ `U U ⇨ A

  ⊢∀ᶜ : ∀ {A B c}
    → renameΣ suc Σ ∣ suc Δ ⊢ c ⦂ A ⇨ B
    → Σ ∣ Δ ⊢ ∀ᶜ c ⦂ `∀ A ⇨ `∀ B

  ⊢⊥ : ∀ {p A B}
    → WfStore Σ
    → WfTy Δ Σ A
    → WfTy Δ Σ B
    → Σ ∣ Δ ⊢ (⊥ᶜ p ⦂ A ⇨ B) ⦂ A ⇨ B
