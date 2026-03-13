module PolyTypes where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

singleTyEnv : Ty → Substᵗ
singleTyEnv B zero    = B
singleTyEnv B (suc i) = ` i

_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

⤊ : Ctx → Ctx
⤊ Γ = map (renameᵗ suc) Γ

-- Replace free X's with U's.
-- The first argument tracks how many type variables are bound.
renameᵘ : ℕ → Renameᵗ → Ty → Ty
renameᵘ d ρ (` i) with d
... | zero = `U (ρ i)
... | suc d' with i
... | zero = ` zero
... | suc j = renameᵗ suc (renameᵘ d' ρ (` j))
renameᵘ d ρ `ℕ              = `ℕ
renameᵘ d ρ `Bool           = `Bool
renameᵘ d ρ `Str            = `Str
renameᵘ d ρ `★              = `★
renameᵘ d ρ (`U u)          = `U u
renameᵘ d ρ (A ⇒ B)         = renameᵘ d ρ A ⇒ renameᵘ d ρ B
renameᵘ d ρ (`∀ A)          = `∀ (renameᵘ (suc d) ρ A)

singleᵘ : Name → Renameᵗ
singleᵘ U zero    = U
singleᵘ U (suc i) = i

_[_]ᵘ : Ty → Name → Ty
A [ U ]ᵘ = renameᵘ 0 (singleᵘ U) A

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

data WfStore : Store → Set where
  wfΣ∅  : WfStore []
  wfΣ∷  : ∀ {Σ A}
    → WfStore Σ
    → WfTy zero Σ A
    → WfStore (A ∷ Σ)

data WfCtx : TyCtx → Store → Ctx → Set where
  wfΓ∅  : ∀ {Δ Σ} → WfCtx Δ Σ []
  wfΓ∷  : ∀ {Δ Σ Γ A}
    → WfCtx Δ Σ Γ
    → WfTy Δ Σ A
    → WfCtx Δ Σ (A ∷ Γ)

data IsVar : Ty → Set where
  U-var    : ∀ {U} → IsVar (`U U)
  X-var  : ∀ {X} → IsVar (` X)
  
------------------------------------------------------------------------
-- Ground types
------------------------------------------------------------------------

data Ground : Ty → Set where
  G-ℕ    : Ground `ℕ
  G-Bool : Ground `Bool
  G-Str  : Ground `Str
  G-⇒★   : Ground (`★ ⇒ `★)
  G-∀★   : Ground (`∀ `★)
  G-var  : ∀ {X} → Ground (` X)
  G-U    : ∀ {U} → Ground (`U U)

IsVar→Ground : ∀ {A}
  → IsVar A
  → Ground A
IsVar→Ground {A} U-var = G-U
IsVar→Ground {A} X-var = G-var

∋ᵁ-unique : ∀ {Σ U A B}
  → Σ ∋ᵁ U ⦂ A
  → Σ ∋ᵁ U ⦂ B
  → A ≡ B
∋ᵁ-unique Zᵁ Zᵁ = refl
∋ᵁ-unique (Sᵁ hA) (Sᵁ hB) = ∋ᵁ-unique hA hB
