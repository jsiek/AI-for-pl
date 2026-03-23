module PolyTypes where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; _≤_; z≤n; s≤s; zero; suc)
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import Data.Bool using (Bool)
open import Data.Product using (_×_; _,_; Σ)

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

-- Substitute `U U` for the X at de Bruijn index d (standard
-- capture-avoiding substitution behavior for surrounding indices).
substᵘ-var : ℕ → Name → Var → Ty
substᵘ-var d U i with d | i
... | zero  | zero  = `U U
... | zero  | suc i = ` i
... | suc d | zero  = ` zero
... | suc d | suc i = renameᵗ suc (substᵘ-var d U i)

substᵘ : ℕ → Name → Ty → Ty
substᵘ d U (` i)            = substᵘ-var d U i
substᵘ d U `ℕ              = `ℕ
substᵘ d U `Bool           = `Bool
substᵘ d U `Str            = `Str
substᵘ d U `★              = `★
substᵘ d U (`U u)          = `U u
substᵘ d U (A ⇒ B)         = substᵘ d U A ⇒ substᵘ d U B
substᵘ d U (`∀ A)          = `∀ (substᵘ (suc d) U A)

singleᵘ : Name → Renameᵗ
singleᵘ U zero    = U
singleᵘ U (suc i) = i

_[_]ᵘ : Ty → Name → Ty
A [ U ]ᵘ = A [ `U U ]ᵗ

substEnvᵘ : ℕ → Name → Substᵗ
substEnvᵘ zero U = singleTyEnv (`U U)
substEnvᵘ (suc d) U = extsᵗ (substEnvᵘ d U)

substEnvᵘ-var :
  ∀ d U X →
  substEnvᵘ d U X ≡ substᵘ-var d U X
substEnvᵘ-var zero U zero = refl
substEnvᵘ-var zero U (suc X) = refl
substEnvᵘ-var (suc d) U zero = refl
substEnvᵘ-var (suc d) U (suc X) =
  cong (renameᵗ suc) (substEnvᵘ-var d U X)

substᵘ-as-substᵗ :
  ∀ d U A →
  substᵘ d U A ≡ substᵗ (substEnvᵘ d U) A
substᵘ-as-substᵗ d U (` X) = sym (substEnvᵘ-var d U X)
substᵘ-as-substᵗ d U `ℕ = refl
substᵘ-as-substᵗ d U `Bool = refl
substᵘ-as-substᵗ d U `Str = refl
substᵘ-as-substᵗ d U `★ = refl
substᵘ-as-substᵗ d U (`U u) = refl
substᵘ-as-substᵗ d U (A ⇒ B) =
  cong₂ _⇒_ (substᵘ-as-substᵗ d U A) (substᵘ-as-substᵗ d U B)
substᵘ-as-substᵗ d U (`∀ A) =
  cong `∀ (substᵘ-as-substᵗ (suc d) U A)

[]ᵘ-as-substᵘ :
  ∀ A U →
  A [ U ]ᵘ ≡ substᵘ 0 U A
[]ᵘ-as-substᵘ A U = sym (substᵘ-as-substᵗ zero U A)

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
  wf⇒    : ∀ {Δ Σ A B}
    → WfTy Δ Σ A
    → WfTy Δ Σ B
    → WfTy Δ Σ (A ⇒ B)
  wf∀    : ∀ {Δ Σ A}
    → WfTy (suc Δ) (renameΣ suc Σ) A
    → WfTy Δ Σ (`∀ A)

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

------------------------------------------------------------------------
-- Types without X variables
------------------------------------------------------------------------

data NoXᵈ : ℕ → Ty → Set where
  NoX-X    : ∀ {d X} → X < d → NoXᵈ d (` X)
  NoX-ℕ    : ∀ {d} → NoXᵈ d `ℕ
  NoX-Bool : ∀ {d} → NoXᵈ d `Bool
  NoX-Str  : ∀ {d} → NoXᵈ d `Str
  NoX-★    : ∀ {d} → NoXᵈ d `★
  NoX-U    : ∀ {d U} → NoXᵈ d (`U U)
  NoX-⇒    : ∀ {d A B} → NoXᵈ d A → NoXᵈ d B → NoXᵈ d (A ⇒ B)
  NoX-∀    : ∀ {d A} → NoXᵈ (suc d) A → NoXᵈ d (`∀ A)

NoX : Ty → Set
NoX A = NoXᵈ zero A

NoXᵈ-suc :
  ∀ {d A} →
  NoXᵈ d A →
  NoXᵈ (suc d) A
NoXᵈ-suc (NoX-X p) = NoX-X (m≤n⇒m≤1+n p)
NoXᵈ-suc NoX-ℕ = NoX-ℕ
NoXᵈ-suc NoX-Bool = NoX-Bool
NoXᵈ-suc NoX-Str = NoX-Str
NoXᵈ-suc NoX-★ = NoX-★
NoXᵈ-suc NoX-U = NoX-U
NoXᵈ-suc (NoX-⇒ nxA nxB) = NoX-⇒ (NoXᵈ-suc nxA) (NoXᵈ-suc nxB)
NoXᵈ-suc (NoX-∀ nxA) = NoX-∀ (NoXᵈ-suc nxA)

NoXᵈ-raise :
  ∀ {d A} →
  NoX A →
  NoXᵈ d A
NoXᵈ-raise {d = zero} nxA = nxA
NoXᵈ-raise {d = suc d} nxA = NoXᵈ-suc (NoXᵈ-raise {d = d} nxA)

Fixes : ℕ → Renameᵗ → Set
Fixes d ρ = ∀ {X} → X < d → ρ X ≡ X

Fixes-0 : ∀ {ρ} → Fixes 0 ρ
Fixes-0 ()

Fixes-ext : ∀ {d ρ} → Fixes d ρ → Fixes (suc d) (extᵗ ρ)
Fixes-ext fix {zero} p = refl
Fixes-ext fix {suc X} (s≤s p) = cong suc (fix p)

NoXᵈ-renameᵗ-id :
  ∀ {d ρ A} →
  Fixes d ρ →
  NoXᵈ d A →
  renameᵗ ρ A ≡ A
NoXᵈ-renameᵗ-id fix (NoX-X p) = cong (λ Y → ` Y) (fix p)
NoXᵈ-renameᵗ-id fix NoX-ℕ = refl
NoXᵈ-renameᵗ-id fix NoX-Bool = refl
NoXᵈ-renameᵗ-id fix NoX-Str = refl
NoXᵈ-renameᵗ-id fix NoX-★ = refl
NoXᵈ-renameᵗ-id fix NoX-U = refl
NoXᵈ-renameᵗ-id fix (NoX-⇒ nxA nxB) =
  cong₂ _⇒_ (NoXᵈ-renameᵗ-id fix nxA) (NoXᵈ-renameᵗ-id fix nxB)
NoXᵈ-renameᵗ-id fix (NoX-∀ nxA) =
  cong `∀ (NoXᵈ-renameᵗ-id (Fixes-ext fix) nxA)

NoXᵈ-renameᵗ :
  ∀ {d ρ A} →
  Fixes d ρ →
  NoXᵈ d A →
  NoXᵈ d (renameᵗ ρ A)
NoXᵈ-renameᵗ fix nxA =
  subst (NoXᵈ _) (sym (NoXᵈ-renameᵗ-id fix nxA)) nxA

NoX-renameᵗ :
  ∀ {ρ A} →
  NoX A →
  NoX (renameᵗ ρ A)
NoX-renameᵗ {ρ = ρ} = NoXᵈ-renameᵗ {ρ = ρ} (Fixes-0 {ρ = ρ})

NoX-renameᵗ-id :
  ∀ {ρ A} →
  NoX A →
  renameᵗ ρ A ≡ A
NoX-renameᵗ-id {ρ = ρ} = NoXᵈ-renameᵗ-id {ρ = ρ} (Fixes-0 {ρ = ρ})

NoX-X-substᵘ-id :
  ∀ {n d U X} →
  X < n →
  n ≤ d →
  substᵘ d U (` X) ≡ ` X
NoX-X-substᵘ-id {n = zero} ()
NoX-X-substᵘ-id {n = suc n} {d = zero} p ()
NoX-X-substᵘ-id {d = suc d} {X = zero} p le = refl
NoX-X-substᵘ-id {n = suc n} {d = suc d} {X = suc X} (s≤s p) (s≤s le) =
  cong (renameᵗ suc) (NoX-X-substᵘ-id {n = n} {d = d} {X = X} p le)

NoXᵈ-substᵘ-id :
  ∀ {n d U A} →
  n ≤ d →
  NoXᵈ n A →
  substᵘ d U A ≡ A
NoXᵈ-substᵘ-id le (NoX-X p) = NoX-X-substᵘ-id p le
NoXᵈ-substᵘ-id le NoX-ℕ = refl
NoXᵈ-substᵘ-id le NoX-Bool = refl
NoXᵈ-substᵘ-id le NoX-Str = refl
NoXᵈ-substᵘ-id le NoX-★ = refl
NoXᵈ-substᵘ-id le NoX-U = refl
NoXᵈ-substᵘ-id le (NoX-⇒ nxA nxB) =
  cong₂ _⇒_ (NoXᵈ-substᵘ-id le nxA) (NoXᵈ-substᵘ-id le nxB)
NoXᵈ-substᵘ-id le (NoX-∀ nxA) =
  cong `∀ (NoXᵈ-substᵘ-id (s≤s le) nxA)

NoXᵈ-substᵘ :
  ∀ {n d U A} →
  n ≤ d →
  NoXᵈ n A →
  NoXᵈ n (substᵘ d U A)
NoXᵈ-substᵘ le nxA =
  subst (NoXᵈ _) (sym (NoXᵈ-substᵘ-id le nxA)) nxA

data VarOrUᵈ (d : ℕ) : Ty → Set where
  VarOrU-U : ∀ {U} → VarOrUᵈ d (`U U)
  VarOrU-X : ∀ {X} → X < d → VarOrUᵈ d (` X)

data VarOrU : Ty → Set where
  VU-U : ∀ {U} → VarOrU (`U U)
  VU-X : ∀ {X} → VarOrU (` X)

substᵘ-var-shape :
  ∀ d U X →
  VarOrU (substᵘ d U (` X))
substᵘ-var-shape zero U zero = VU-U
substᵘ-var-shape zero U (suc X) = VU-X
substᵘ-var-shape (suc d) U zero = VU-X
substᵘ-var-shape (suc d) U (suc X)
  with substᵘ d U (` X) | substᵘ-var-shape d U X
... | `U u | VU-U = VU-U
... | ` y  | VU-X = VU-X

inst-var-shape :
  ∀ {n U X} →
  X < suc n →
  VarOrUᵈ n (substᵘ n U (` X))
inst-var-shape {n = zero} {X = zero} p = VarOrU-U
inst-var-shape {n = zero} {X = suc X} (s≤s ())
inst-var-shape {n = suc n} {X = zero} p = VarOrU-X (s≤s z≤n)
inst-var-shape {n = suc n} {U = U} {X = suc X} (s≤s p)
  with substᵘ n U (` X) | inst-var-shape {n = n} {U = U} {X = X} p
... | `U u | VarOrU-U = VarOrU-U
... | ` y  | VarOrU-X q = VarOrU-X (s≤s q)

NoXᵈ-inst-var :
  ∀ {n U X} →
  X < suc n →
  NoXᵈ n (substᵘ n U (` X))
NoXᵈ-inst-var {n = n} {U = U} {X = X} p
  with substᵘ n U (` X) | inst-var-shape {n = n} {U = U} {X = X} p
... | `U u | VarOrU-U = NoX-U
... | ` y  | VarOrU-X q = NoX-X q

NoXᵈ-inst :
  ∀ {n A U} →
  NoXᵈ (suc n) A →
  NoXᵈ n (substᵘ n U A)
NoXᵈ-inst (NoX-X p) = NoXᵈ-inst-var p
NoXᵈ-inst NoX-ℕ = NoX-ℕ
NoXᵈ-inst NoX-Bool = NoX-Bool
NoXᵈ-inst NoX-Str = NoX-Str
NoXᵈ-inst NoX-★ = NoX-★
NoXᵈ-inst NoX-U = NoX-U
NoXᵈ-inst (NoX-⇒ nxA nxB) = NoX-⇒ (NoXᵈ-inst nxA) (NoXᵈ-inst nxB)
NoXᵈ-inst {n = n} (NoX-∀ nxA) = NoX-∀ (NoXᵈ-inst {n = suc n} nxA)

NoXᵈ-close-var :
  ∀ n U X →
  NoXᵈ n (substᵘ n U (` X)) →
  X < suc n
NoXᵈ-close-var zero U zero NoX-U = s≤s z≤n
NoXᵈ-close-var zero U (suc X) (NoX-X ())
NoXᵈ-close-var (suc n) U zero (NoX-X p) = s≤s z≤n
NoXᵈ-close-var (suc n) U (suc X) nx
  with substᵘ n U (` X) in eq | substᵘ-var-shape n U X
... | `U u | VU-U =
  s≤s (NoXᵈ-close-var n U X (subst (NoXᵈ n) (sym eq) NoX-U))
... | ` y  | VU-X
  with nx
... | NoX-X (s≤s p) =
  s≤s (NoXᵈ-close-var n U X (subst (NoXᵈ n) (sym eq) (NoX-X p)))

NoXᵈ-close :
  ∀ {n U A} →
  NoXᵈ n (substᵘ n U A) →
  NoXᵈ (suc n) A
NoXᵈ-close {n = n} {U = U} {A = ` X} nx =
  NoX-X (NoXᵈ-close-var n U X nx)
NoXᵈ-close {A = `ℕ} NoX-ℕ = NoX-ℕ
NoXᵈ-close {A = `Bool} NoX-Bool = NoX-Bool
NoXᵈ-close {A = `Str} NoX-Str = NoX-Str
NoXᵈ-close {A = `★} NoX-★ = NoX-★
NoXᵈ-close {A = `U U} NoX-U = NoX-U
NoXᵈ-close {A = A ⇒ B} (NoX-⇒ nxA nxB) =
  NoX-⇒ (NoXᵈ-close {A = A} nxA) (NoXᵈ-close {A = B} nxB)
NoXᵈ-close {n = n} {U = U} {A = `∀ A} (NoX-∀ nxA) =
  NoX-∀ (NoXᵈ-close {n = suc n} {U = U} {A = A} nxA)

NoX-openᵘ :
  ∀ {A U} →
  NoXᵈ 1 A →
  NoX (A [ U ]ᵘ)
NoX-openᵘ {A} {U} nxA =
  subst NoX (sym ([]ᵘ-as-substᵘ A U)) (NoXᵈ-inst {n = zero} {U = U} nxA)

NoX-[]ᵘ :
  ∀ {A U} →
  NoX A →
  NoX (A [ U ]ᵘ)
NoX-[]ᵘ {A} {U} nxA = NoX-openᵘ {A = A} {U = U} (NoXᵈ-suc nxA)

------------------------------------------------------------------------
-- Type consistency
------------------------------------------------------------------------

infix 4 _~_

data _~_ : Ty → Ty → Set where
  ~-X    : ∀ {X} → ` X ~ ` X
  ~-ℕ    : `ℕ ~ `ℕ
  ~-Bool : `Bool ~ `Bool
  ~-Str  : `Str ~ `Str
  ~-★    : `★ ~ `★
  ~-U    : ∀ {U} → `U U ~ `U U

  ★~ℕ    : `★ ~ `ℕ
  ℕ~★    : `ℕ ~ `★
  ★~Bool : `★ ~ `Bool
  Bool~★ : `Bool ~ `★
  ★~Str  : `★ ~ `Str
  Str~★  : `Str ~ `★
  ★~U    : ∀ {U} → `★ ~ `U U
  U~★    : ∀ {U} → `U U ~ `★

  ★~⇒ : ∀ {A B}
    → A ~ `★
    → `★ ~ B
    → `★ ~ (A ⇒ B)

  ⇒~★ : ∀ {A B}
    → `★ ~ A
    → B ~ `★
    → (A ⇒ B) ~ `★

  ★~∀ : ∀ {A}
    → `★ ~ A [ 0 ]ᵘ
    → `★ ~ `∀ A

  ∀~★ : ∀ {A}
    → A [ 0 ]ᵘ ~ `★
    → `∀ A ~ `★

  ~-⇒ : ∀ {A B C D}
    → C ~ A
    → B ~ D
    → (A ⇒ B) ~ (C ⇒ D)

  ~-∀ : ∀ {A B}
    → A ~ B
    → `∀ A ~ `∀ B

~-sym : ∀ {A B}
  → A ~ B
  → B ~ A
~-sym ~-X = ~-X
~-sym ~-ℕ = ~-ℕ
~-sym ~-Bool = ~-Bool
~-sym ~-Str = ~-Str
~-sym ~-★ = ~-★
~-sym ~-U = ~-U
~-sym ★~ℕ = ℕ~★
~-sym ℕ~★ = ★~ℕ
~-sym ★~Bool = Bool~★
~-sym Bool~★ = ★~Bool
~-sym ★~Str = Str~★
~-sym Str~★ = ★~Str
~-sym ★~U = U~★
~-sym U~★ = ★~U
~-sym (★~⇒ A~★ ★~B) = ⇒~★ (~-sym A~★) (~-sym ★~B)
~-sym (⇒~★ ★~A B~★) = ★~⇒ (~-sym ★~A) (~-sym B~★)
~-sym (★~∀ ★~A) = ∀~★ (~-sym ★~A)
~-sym (∀~★ A~★) = ★~∀ (~-sym A~★)
~-sym (~-⇒ C~A B~D) = ~-⇒ (~-sym C~A) (~-sym B~D)
~-sym (~-∀ A~B) = ~-∀ (~-sym A~B)

~-refl : ∀ {A} → A ~ A
~-refl {A = ` X} = ~-X
~-refl {A = `ℕ} = ~-ℕ
~-refl {A = `Bool} = ~-Bool
~-refl {A = `Str} = ~-Str
~-refl {A = `★} = ~-★
~-refl {A = `U U} = ~-U
~-refl {A = A ⇒ B} = ~-⇒ ~-refl ~-refl
~-refl {A = `∀ A} = ~-∀ ~-refl

{-# TERMINATING #-}
mutual
  ★~-ty : ∀ A → NoX A → `★ ~ A
  ★~-ty (` X) (NoX-X ())
  ★~-ty `ℕ NoX-ℕ = ★~ℕ
  ★~-ty `Bool NoX-Bool = ★~Bool
  ★~-ty `Str NoX-Str = ★~Str
  ★~-ty `★ NoX-★ = ~-★
  ★~-ty (`U U) NoX-U = ★~U
  ★~-ty (A ⇒ B) (NoX-⇒ nxA nxB) = ★~⇒ (~★-ty A nxA) (★~-ty B nxB)
  ★~-ty (`∀ A) (NoX-∀ nxA) =
    ★~∀
      (★~-ty (A [ 0 ]ᵘ) (NoX-openᵘ nxA))

  ~★-ty : ∀ A → NoX A → A ~ `★
  ~★-ty (` X) (NoX-X ())
  ~★-ty `ℕ NoX-ℕ = ℕ~★
  ~★-ty `Bool NoX-Bool = Bool~★
  ~★-ty `Str NoX-Str = Str~★
  ~★-ty `★ NoX-★ = ~-★
  ~★-ty (`U U) NoX-U = U~★
  ~★-ty (A ⇒ B) (NoX-⇒ nxA nxB) = ⇒~★ (★~-ty A nxA) (~★-ty B nxB)
  ~★-ty (`∀ A) (NoX-∀ nxA) =
    ∀~★
      (~★-ty (A [ 0 ]ᵘ) (NoX-openᵘ nxA))

WfTy→NoXᵈ :
  ∀ {Δ Σ A} →
  WfTy Δ Σ A →
  NoXᵈ Δ A
WfTy→NoXᵈ (wfVar x<Δ) = NoX-X x<Δ
WfTy→NoXᵈ wfℕ = NoX-ℕ
WfTy→NoXᵈ wfBool = NoX-Bool
WfTy→NoXᵈ wfStr = NoX-Str
WfTy→NoXᵈ wf★ = NoX-★
WfTy→NoXᵈ (wfU hU) = NoX-U
WfTy→NoXᵈ (wf⇒ hA hB) = NoX-⇒ (WfTy→NoXᵈ hA) (WfTy→NoXᵈ hB)
WfTy→NoXᵈ (wf∀ hA) = NoX-∀ (WfTy→NoXᵈ hA)

mutual
  ★~-NoX :
    ∀ {A} →
    `★ ~ A →
    NoX A
  ★~-NoX ~-★ = NoX-★
  ★~-NoX ★~ℕ = NoX-ℕ
  ★~-NoX ★~Bool = NoX-Bool
  ★~-NoX ★~Str = NoX-Str
  ★~-NoX ★~U = NoX-U
  ★~-NoX (★~⇒ A~★ ★~B) = NoX-⇒ (~★-NoX A~★) (★~-NoX ★~B)
  ★~-NoX (★~∀ {A} ★~A[0]) =
    NoX-∀
      (NoXᵈ-close {n = zero} {U = zero} {A = A}
        (subst NoX ([]ᵘ-as-substᵘ A 0) (★~-NoX ★~A[0])))

  ~★-NoX :
    ∀ {A} →
    A ~ `★ →
    NoX A
  ~★-NoX ~-★ = NoX-★
  ~★-NoX ℕ~★ = NoX-ℕ
  ~★-NoX Bool~★ = NoX-Bool
  ~★-NoX Str~★ = NoX-Str
  ~★-NoX U~★ = NoX-U
  ~★-NoX (⇒~★ ★~A B~★) = NoX-⇒ (★~-NoX ★~A) (~★-NoX B~★)
  ~★-NoX (∀~★ {A} A[0]~★) =
    NoX-∀
      (NoXᵈ-close {n = zero} {U = zero} {A = A}
        (subst NoX ([]ᵘ-as-substᵘ A 0) (~★-NoX A[0]~★)))

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

------------------------------------------------------------------------
-- Type precision and consistency-as-LUB
------------------------------------------------------------------------

infix 4 _⊑_

data _⊑_ : Ty → Ty → Set where
  ⊑-X : ∀ {X} → ` X ⊑ ` X
  ⊑-ℕ : `ℕ ⊑ `ℕ
  ⊑-Bool : `Bool ⊑ `Bool
  ⊑-Str : `Str ⊑ `Str
  ⊑-U : ∀ {U} → `U U ⊑ `U U
  ⊑-★ : ∀ {A} → NoX A → `★ ⊑ A
  ⊑-⇒ : ∀ {A B C D} → A ⊑ C → B ⊑ D → (A ⇒ B) ⊑ (C ⇒ D)
  ⊑-∀ : ∀ {A B} → A ⊑ B → `∀ A ⊑ `∀ B

⊑-refl : ∀ {A} → A ⊑ A
⊑-refl {A = ` X} = ⊑-X
⊑-refl {A = `ℕ} = ⊑-ℕ
⊑-refl {A = `Bool} = ⊑-Bool
⊑-refl {A = `Str} = ⊑-Str
⊑-refl {A = `★} = ⊑-★ NoX-★
⊑-refl {A = `U U} = ⊑-U
⊑-refl {A = A ⇒ B} = ⊑-⇒ ⊑-refl ⊑-refl
⊑-refl {A = `∀ A} = ⊑-∀ ⊑-refl

⊑-NoX-leftᵈ : ∀ {d A B} → A ⊑ B → NoXᵈ d B → NoXᵈ d A
⊑-NoX-leftᵈ ⊑-X (NoX-X p) = NoX-X p
⊑-NoX-leftᵈ ⊑-ℕ NoX-ℕ = NoX-ℕ
⊑-NoX-leftᵈ ⊑-Bool NoX-Bool = NoX-Bool
⊑-NoX-leftᵈ ⊑-Str NoX-Str = NoX-Str
⊑-NoX-leftᵈ ⊑-U NoX-U = NoX-U
⊑-NoX-leftᵈ (⊑-★ nxB) nxB' = NoX-★
⊑-NoX-leftᵈ (⊑-⇒ A⊑C B⊑D) (NoX-⇒ nxC nxD) =
  NoX-⇒ (⊑-NoX-leftᵈ A⊑C nxC) (⊑-NoX-leftᵈ B⊑D nxD)
⊑-NoX-leftᵈ {d = d} (⊑-∀ A⊑B) (NoX-∀ nxB) =
  NoX-∀ (⊑-NoX-leftᵈ {d = suc d} A⊑B nxB)

⊑-NoX-rightᵈ : ∀ {d A B} → NoXᵈ d A → A ⊑ B → NoXᵈ d B
⊑-NoX-rightᵈ (NoX-X p) ⊑-X = NoX-X p
⊑-NoX-rightᵈ NoX-ℕ ⊑-ℕ = NoX-ℕ
⊑-NoX-rightᵈ NoX-Bool ⊑-Bool = NoX-Bool
⊑-NoX-rightᵈ NoX-Str ⊑-Str = NoX-Str
⊑-NoX-rightᵈ {d = d} NoX-★ (⊑-★ nxB) = NoXᵈ-raise {d = d} nxB
⊑-NoX-rightᵈ NoX-U ⊑-U = NoX-U
⊑-NoX-rightᵈ (NoX-⇒ nxA nxB) (⊑-⇒ A⊑C B⊑D) =
  NoX-⇒ (⊑-NoX-rightᵈ nxA A⊑C) (⊑-NoX-rightᵈ nxB B⊑D)
⊑-NoX-rightᵈ {d = d} (NoX-∀ nxA) (⊑-∀ A⊑B) =
  NoX-∀ (⊑-NoX-rightᵈ {d = suc d} nxA A⊑B)

⊑-NoX-left : ∀ {A B} → A ⊑ B → NoX B → NoX A
⊑-NoX-left = ⊑-NoX-leftᵈ

⊑-NoX-right : ∀ {A B} → NoX A → A ⊑ B → NoX B
⊑-NoX-right = ⊑-NoX-rightᵈ

⊑-trans : ∀ {A B C} → A ⊑ B → B ⊑ C → A ⊑ C
⊑-trans ⊑-X ⊑-X = ⊑-X
⊑-trans ⊑-ℕ ⊑-ℕ = ⊑-ℕ
⊑-trans ⊑-Bool ⊑-Bool = ⊑-Bool
⊑-trans ⊑-Str ⊑-Str = ⊑-Str
⊑-trans ⊑-U ⊑-U = ⊑-U
⊑-trans (⊑-★ nxB) B⊑C = ⊑-★ (⊑-NoX-right nxB B⊑C)
⊑-trans (⊑-⇒ A⊑B B⊑D) (⊑-⇒ B⊑C D⊑E) =
  ⊑-⇒ (⊑-trans A⊑B B⊑C) (⊑-trans B⊑D D⊑E)
⊑-trans (⊑-∀ A⊑B) (⊑-∀ B⊑C) = ⊑-∀ (⊑-trans A⊑B B⊑C)

★⊑→NoX : ∀ {A} → `★ ⊑ A → NoX A
★⊑→NoX p = ⊑-NoX-right NoX-★ p

★⊑⇒-dom : ∀ {A B} → `★ ⊑ (A ⇒ B) → `★ ⊑ A
★⊑⇒-dom ★⊑A⇒B with ★⊑→NoX ★⊑A⇒B
... | NoX-⇒ nxA nxB = ⊑-★ nxA

★⊑⇒-cod : ∀ {A B} → `★ ⊑ (A ⇒ B) → `★ ⊑ B
★⊑⇒-cod ★⊑A⇒B with ★⊑→NoX ★⊑A⇒B
... | NoX-⇒ nxA nxB = ⊑-★ nxB

★⊑∀-open : ∀ {A U} → `★ ⊑ (`∀ A) → `★ ⊑ (A [ U ]ᵘ)
★⊑∀-open {A} {U} ★⊑∀A with ★⊑→NoX ★⊑∀A
... | NoX-∀ nxA = ⊑-★ (NoX-openᵘ {A = A} {U = U} nxA)

upper-bounds-consistent : ∀ {A B C} → A ⊑ C → B ⊑ C → A ~ B
upper-bounds-consistent ⊑-X ⊑-X = ~-X
upper-bounds-consistent ⊑-ℕ ⊑-ℕ = ~-ℕ
upper-bounds-consistent {A = `ℕ} pA (⊑-★ nxC) =
  ~★-ty `ℕ (⊑-NoX-left pA nxC)
upper-bounds-consistent ⊑-Bool ⊑-Bool = ~-Bool
upper-bounds-consistent {A = `Bool} pA (⊑-★ nxC) =
  ~★-ty `Bool (⊑-NoX-left pA nxC)
upper-bounds-consistent ⊑-Str ⊑-Str = ~-Str
upper-bounds-consistent {A = `Str} pA (⊑-★ nxC) =
  ~★-ty `Str (⊑-NoX-left pA nxC)
upper-bounds-consistent ⊑-U ⊑-U = ~-U
upper-bounds-consistent {A = `U U} pA (⊑-★ nxC) =
  ~★-ty (`U U) (⊑-NoX-left pA nxC)
upper-bounds-consistent (⊑-★ nxC) pB =
  ★~-ty _ (⊑-NoX-left pB nxC)
upper-bounds-consistent pA (⊑-★ nxC) =
  ~★-ty _ (⊑-NoX-left pA nxC)
upper-bounds-consistent (⊑-⇒ A⊑C B⊑D) (⊑-⇒ A'⊑C B'⊑D) =
  ~-⇒
    (upper-bounds-consistent A'⊑C A⊑C)
    (upper-bounds-consistent B⊑D B'⊑D)
upper-bounds-consistent (⊑-∀ A⊑C) (⊑-∀ B⊑C) =
  ~-∀ (upper-bounds-consistent A⊑C B⊑C)

Lub : Ty → Ty → Ty → Set
Lub A B C =
  (A ⊑ C) × ((B ⊑ C) × (∀ {D} → A ⊑ D → B ⊑ D → C ⊑ D))

mkLub :
  ∀ {A B C} →
  A ⊑ C →
  B ⊑ C →
  (∀ {D} → A ⊑ D → B ⊑ D → C ⊑ D) →
  Lub A B C
mkLub A⊑C B⊑C least = A⊑C , (B⊑C , least)

mutual
  consistency→lub :
    ∀ {A B} → A ~ B → Σ Ty (Lub A B)
  consistency→lub {A = ` X} ~-X =
    ` X , mkLub ⊑-X ⊑-X (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-ℕ =
    `ℕ , mkLub ⊑-ℕ ⊑-ℕ (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-Bool =
    `Bool , mkLub ⊑-Bool ⊑-Bool (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-Str =
    `Str , mkLub ⊑-Str ⊑-Str (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-★ =
    `★ , mkLub (⊑-★ NoX-★) (⊑-★ NoX-★) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-U =
    `U _ , mkLub ⊑-U ⊑-U (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~ℕ =
    `ℕ , mkLub (⊑-★ NoX-ℕ) ⊑-ℕ (λ A⊑D B⊑D → B⊑D)
  consistency→lub ℕ~★ =
    `ℕ , mkLub ⊑-ℕ (⊑-★ NoX-ℕ) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~Bool =
    `Bool , mkLub (⊑-★ NoX-Bool) ⊑-Bool (λ A⊑D B⊑D → B⊑D)
  consistency→lub Bool~★ =
    `Bool , mkLub ⊑-Bool (⊑-★ NoX-Bool) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~Str =
    `Str , mkLub (⊑-★ NoX-Str) ⊑-Str (λ A⊑D B⊑D → B⊑D)
  consistency→lub Str~★ =
    `Str , mkLub ⊑-Str (⊑-★ NoX-Str) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~U =
    `U _ , mkLub (⊑-★ NoX-U) ⊑-U (λ A⊑D B⊑D → B⊑D)
  consistency→lub U~★ =
    `U _ , mkLub ⊑-U (⊑-★ NoX-U) (λ A⊑D B⊑D → A⊑D)
  consistency→lub (★~⇒ A~★ ★~B)
    with ★~-NoX (★~⇒ A~★ ★~B)
  ... | NoX-⇒ nxA nxB =
    (_ ⇒ _) ,
    mkLub (⊑-★ (NoX-⇒ nxA nxB)) (⊑-⇒ ⊑-refl ⊑-refl)
      (λ A⊑D B⊑D → B⊑D)
  consistency→lub (⇒~★ ★~A B~★)
    with ~★-NoX (⇒~★ ★~A B~★)
  ... | NoX-⇒ nxA nxB =
    (_ ⇒ _) ,
    mkLub (⊑-⇒ ⊑-refl ⊑-refl) (⊑-★ (NoX-⇒ nxA nxB))
      (λ A⊑D B⊑D → A⊑D)
  consistency→lub {A = A₁ ⇒ B₁} {B = C₁ ⇒ D₁} (~-⇒ C~A B~D)
    with consistency→lub C~A
       | consistency→lub B~D
  ... | Jdom , (C⊑Jdom , (A⊑Jdom , leastDom))
      | Jcod , (B⊑Jcod , (D⊑Jcod , leastCod)) =
    (Jdom ⇒ Jcod) ,
    mkLub (⊑-⇒ A⊑Jdom B⊑Jcod) (⊑-⇒ C⊑Jdom D⊑Jcod) least
    where
      least :
        ∀ {X} →
        (A₁ ⇒ B₁) ⊑ X →
        (C₁ ⇒ D₁) ⊑ X →
        (Jdom ⇒ Jcod) ⊑ X
      least (⊑-⇒ A⊑X B⊑X) (⊑-⇒ C⊑X D⊑X) =
        ⊑-⇒ (leastDom C⊑X A⊑X) (leastCod B⊑X D⊑X)
  consistency→lub {A = `∀ A₀} {B = `∀ B₀} (~-∀ A~B)
    with consistency→lub A~B
  ... | J , (A⊑J , (B⊑J , leastBody)) =
    `∀ J , mkLub (⊑-∀ A⊑J) (⊑-∀ B⊑J) least
    where
      least : ∀ {X} → `∀ A₀ ⊑ X → `∀ B₀ ⊑ X → `∀ J ⊑ X
      least (⊑-∀ A⊑X) (⊑-∀ B⊑X) =
        ⊑-∀ (leastBody A⊑X B⊑X)
  consistency→lub (★~∀ ★~A)
    with ★~-NoX (★~∀ ★~A)
  ... | NoX-∀ nxA = `∀ _ ,
    mkLub (⊑-★ (NoX-∀ nxA)) (⊑-∀ ⊑-refl) (λ A⊑D B⊑D → B⊑D)
  consistency→lub (∀~★ A~★)
    with ~★-NoX (∀~★ A~★)
  ... | NoX-∀ nxA = `∀ _ ,
    mkLub (⊑-∀ ⊑-refl) (⊑-★ (NoX-∀ nxA)) (λ A⊑D B⊑D → A⊑D)

lub→consistency : ∀ {A B} → Σ Ty (Lub A B) → A ~ B
lub→consistency (_ , (A⊑C , (B⊑C , least))) =
  upper-bounds-consistent A⊑C B⊑C

consistency-iff-lub :
  ∀ {A B} →
  (A ~ B → Σ Ty (Lub A B)) ×
  (Σ Ty (Lub A B) → A ~ B)
consistency-iff-lub =
  (λ A~B → consistency→lub A~B) , lub→consistency

app-consistency :
  ∀ {A B A′ B′} →
  A′ ⊑ A →
  A ~ B →
  B′ ⊑ B →
  A′ ~ B′
app-consistency A′⊑A A~B B′⊑B
  with consistency→lub A~B
... | C , (A⊑C , (B⊑C , least)) =
  upper-bounds-consistent (⊑-trans A′⊑A A⊑C) (⊑-trans B′⊑B B⊑C)

prec-left :
  ∀ {X A B} →
  X ⊑ A →
  A ~ B →
  X ~ B
prec-left X⊑A A~B = app-consistency X⊑A A~B ⊑-refl

prec-right :
  ∀ {A B Y} →
  A ~ B →
  Y ⊑ B →
  A ~ Y
prec-right A~B Y⊑B = app-consistency ⊑-refl A~B Y⊑B

------------------------------------------------------------------------
-- Renaming and substitution preserves precision 
------------------------------------------------------------------------

⊑-renameᵗ : ∀ {ρ A B} → A ⊑ B → renameᵗ ρ A ⊑ renameᵗ ρ B
⊑-renameᵗ ⊑-X = ⊑-X
⊑-renameᵗ ⊑-ℕ = ⊑-ℕ
⊑-renameᵗ ⊑-Bool = ⊑-Bool
⊑-renameᵗ ⊑-Str = ⊑-Str
⊑-renameᵗ ⊑-U = ⊑-U
⊑-renameᵗ (⊑-★ nxB) = ⊑-★ (NoX-renameᵗ nxB)
⊑-renameᵗ (⊑-⇒ A⊑C B⊑D) = ⊑-⇒ (⊑-renameᵗ A⊑C) (⊑-renameᵗ B⊑D)
⊑-renameᵗ {ρ = ρ} (⊑-∀ A⊑B) = ⊑-∀ (⊑-renameᵗ {ρ = extᵗ ρ} A⊑B)

⊑-substᵘ : ∀ {d U A B} → A ⊑ B → substᵘ d U A ⊑ substᵘ d U B
⊑-substᵘ {d = d} {U = U} {A = ` X} ⊑-X
  with substᵘ d U (` X) | substᵘ-var-shape d U X
... | `U u | VU-U = ⊑-U
... | ` y  | VU-X = ⊑-X
⊑-substᵘ ⊑-ℕ = ⊑-ℕ
⊑-substᵘ ⊑-Bool = ⊑-Bool
⊑-substᵘ ⊑-Str = ⊑-Str
⊑-substᵘ ⊑-U = ⊑-U
⊑-substᵘ {d = d} {U = U} (⊑-★ nxB) = ⊑-★ (NoXᵈ-substᵘ {d = d} {U = U} z≤n nxB)
⊑-substᵘ (⊑-⇒ A⊑C B⊑D) = ⊑-⇒ (⊑-substᵘ A⊑C) (⊑-substᵘ B⊑D)
⊑-substᵘ {d = d} {U = U} (⊑-∀ A⊑B) =
  ⊑-∀ (⊑-substᵘ {d = suc d} {U = U} A⊑B)

⊑-[]ᵘ : ∀ {A B U} → A ⊑ B → A [ U ]ᵘ ⊑ B [ U ]ᵘ
⊑-[]ᵘ {A = A} {B = B} {U = U} A⊑B
  rewrite []ᵘ-as-substᵘ A U | []ᵘ-as-substᵘ B U
  = ⊑-substᵘ {d = zero} {U = U} A⊑B

------------------------------------------------------------------------
-- Alternative precision with specialized `★`-left rules
------------------------------------------------------------------------

infix 4 _⊑′_

data _⊑′_ : Ty → Ty → Set where
  ⊑′-X : ∀ {X} → ` X ⊑′ ` X
  ⊑′-ℕ : `ℕ ⊑′ `ℕ
  ⊑′-Bool : `Bool ⊑′ `Bool
  ⊑′-Str : `Str ⊑′ `Str
  ⊑′-★ : `★ ⊑′ `★
  ⊑′-U : ∀ {U} → `U U ⊑′ `U U
  ★⊑′ℕ : `★ ⊑′ `ℕ
  ★⊑′Bool : `★ ⊑′ `Bool
  ★⊑′Str : `★ ⊑′ `Str
  ★⊑′U : ∀ {U} → `★ ⊑′ `U U
  ★⊑′⇒ : ∀ {A B} → `★ ⊑′ A → `★ ⊑′ B → `★ ⊑′ (A ⇒ B)
  ★⊑′∀ : ∀ {A} → `★ ⊑′ (A [ 0 ]ᵘ) → `★ ⊑′ `∀ A
  ⊑′-⇒ : ∀ {A B C D} → A ⊑′ C → B ⊑′ D → (A ⇒ B) ⊑′ (C ⇒ D)
  ⊑′-∀ : ∀ {A B} → A ⊑′ B → `∀ A ⊑′ `∀ B

{-# TERMINATING #-}
NoX→★⊑′ : ∀ {A} → NoX A → `★ ⊑′ A
NoX→★⊑′ (NoX-X ())
NoX→★⊑′ NoX-ℕ = ★⊑′ℕ
NoX→★⊑′ NoX-Bool = ★⊑′Bool
NoX→★⊑′ NoX-Str = ★⊑′Str
NoX→★⊑′ NoX-★ = ⊑′-★
NoX→★⊑′ NoX-U = ★⊑′U
NoX→★⊑′ (NoX-⇒ nxA nxB) = ★⊑′⇒ (NoX→★⊑′ nxA) (NoX→★⊑′ nxB)
NoX→★⊑′ (NoX-∀ nxA) = ★⊑′∀ (NoX→★⊑′ (NoX-openᵘ nxA))

★⊑′→NoX : ∀ {A} → `★ ⊑′ A → NoX A
★⊑′→NoX ⊑′-★ = NoX-★
★⊑′→NoX ★⊑′ℕ = NoX-ℕ
★⊑′→NoX ★⊑′Bool = NoX-Bool
★⊑′→NoX ★⊑′Str = NoX-Str
★⊑′→NoX ★⊑′U = NoX-U
★⊑′→NoX (★⊑′⇒ ★⊑′A ★⊑′B) =
  NoX-⇒ (★⊑′→NoX ★⊑′A) (★⊑′→NoX ★⊑′B)
★⊑′→NoX {A = `∀ A} (★⊑′∀ ★⊑′A[0]) =
  NoX-∀
    (NoXᵈ-close {n = zero} {U = zero} {A = A}
      (subst NoX ([]ᵘ-as-substᵘ A 0) (★⊑′→NoX ★⊑′A[0])))

⊑→⊑′ : ∀ {A B} → A ⊑ B → A ⊑′ B
⊑→⊑′ ⊑-X = ⊑′-X
⊑→⊑′ ⊑-ℕ = ⊑′-ℕ
⊑→⊑′ ⊑-Bool = ⊑′-Bool
⊑→⊑′ ⊑-Str = ⊑′-Str
⊑→⊑′ ⊑-U = ⊑′-U
⊑→⊑′ (⊑-★ nxA) = NoX→★⊑′ nxA
⊑→⊑′ (⊑-⇒ A⊑C B⊑D) = ⊑′-⇒ (⊑→⊑′ A⊑C) (⊑→⊑′ B⊑D)
⊑→⊑′ (⊑-∀ A⊑B) = ⊑′-∀ (⊑→⊑′ A⊑B)

⊑′→⊑ : ∀ {A B} → A ⊑′ B → A ⊑ B
⊑′→⊑ ⊑′-X = ⊑-X
⊑′→⊑ ⊑′-ℕ = ⊑-ℕ
⊑′→⊑ ⊑′-Bool = ⊑-Bool
⊑′→⊑ ⊑′-Str = ⊑-Str
⊑′→⊑ p@⊑′-★ = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ ⊑′-U = ⊑-U
⊑′→⊑ p@★⊑′ℕ = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ p@★⊑′Bool = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ p@★⊑′Str = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ p@★⊑′U = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ p@(★⊑′⇒ ★⊑′A ★⊑′B) = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ p@(★⊑′∀ ★⊑′A[0]) = ⊑-★ (★⊑′→NoX p)
⊑′→⊑ (⊑′-⇒ A⊑′C B⊑′D) = ⊑-⇒ (⊑′→⊑ A⊑′C) (⊑′→⊑ B⊑′D)
⊑′→⊑ (⊑′-∀ A⊑′B) = ⊑-∀ (⊑′→⊑ A⊑′B)

⊑′-renameᵗ : ∀ {ρ A B} → A ⊑′ B → renameᵗ ρ A ⊑′ renameᵗ ρ B
⊑′-renameᵗ A⊑′B = ⊑→⊑′ (⊑-renameᵗ (⊑′→⊑ A⊑′B))

⊑′-substᵘ : ∀ {d U A B} → A ⊑′ B → substᵘ d U A ⊑′ substᵘ d U B
⊑′-substᵘ A⊑′B = ⊑→⊑′ (⊑-substᵘ (⊑′→⊑ A⊑′B))

⊑′-[]ᵘ : ∀ {A B U} → A ⊑′ B → A [ U ]ᵘ ⊑′ B [ U ]ᵘ
⊑′-[]ᵘ {A = A} {B = B} {U = U} A⊑′B
  rewrite []ᵘ-as-substᵘ A U | []ᵘ-as-substᵘ B U
  = ⊑′-substᵘ {d = zero} {U = U} A⊑′B

★⊑′⇒-dom : ∀ {A B} → `★ ⊑′ (A ⇒ B) → `★ ⊑′ A
★⊑′⇒-dom ★⊑′A⇒B with ★⊑′→NoX ★⊑′A⇒B
... | NoX-⇒ nxA nxB = NoX→★⊑′ nxA

★⊑′⇒-cod : ∀ {A B} → `★ ⊑′ (A ⇒ B) → `★ ⊑′ B
★⊑′⇒-cod ★⊑′A⇒B with ★⊑′→NoX ★⊑′A⇒B
... | NoX-⇒ nxA nxB = NoX→★⊑′ nxB

★⊑′∀-open : ∀ {A U} → `★ ⊑′ (`∀ A) → `★ ⊑′ (A [ U ]ᵘ)
★⊑′∀-open {A} {U} ★⊑′∀A with ★⊑′→NoX ★⊑′∀A
... | NoX-∀ nxA = NoX→★⊑′ (NoX-openᵘ {A = A} {U = U} nxA)

⊑′-refl : ∀ {A} → A ⊑′ A
⊑′-refl = ⊑→⊑′ ⊑-refl

⊑′-NoX-leftᵈ : ∀ {d A B} → A ⊑′ B → NoXᵈ d B → NoXᵈ d A
⊑′-NoX-leftᵈ A⊑′B nxB = ⊑-NoX-leftᵈ (⊑′→⊑ A⊑′B) nxB

⊑′-NoX-rightᵈ : ∀ {d A B} → NoXᵈ d A → A ⊑′ B → NoXᵈ d B
⊑′-NoX-rightᵈ nxA A⊑′B = ⊑-NoX-rightᵈ nxA (⊑′→⊑ A⊑′B)

⊑′-NoX-left : ∀ {A B} → A ⊑′ B → NoX B → NoX A
⊑′-NoX-left = ⊑′-NoX-leftᵈ

⊑′-NoX-right : ∀ {A B} → NoX A → A ⊑′ B → NoX B
⊑′-NoX-right = ⊑′-NoX-rightᵈ

⊑′-trans : ∀ {A B C} → A ⊑′ B → B ⊑′ C → A ⊑′ C
⊑′-trans A⊑′B B⊑′C = ⊑→⊑′ (⊑-trans (⊑′→⊑ A⊑′B) (⊑′→⊑ B⊑′C))

upper-bounds-consistent′ : ∀ {A B C} → A ⊑′ C → B ⊑′ C → A ~ B
upper-bounds-consistent′ A⊑′C B⊑′C =
  upper-bounds-consistent (⊑′→⊑ A⊑′C) (⊑′→⊑ B⊑′C)

Lub′ : Ty → Ty → Ty → Set
Lub′ A B C =
  (A ⊑′ C) × ((B ⊑′ C) × (∀ {D} → A ⊑′ D → B ⊑′ D → C ⊑′ D))

mkLub′ :
  ∀ {A B C} →
  A ⊑′ C →
  B ⊑′ C →
  (∀ {D} → A ⊑′ D → B ⊑′ D → C ⊑′ D) →
  Lub′ A B C
mkLub′ A⊑′C B⊑′C least = A⊑′C , (B⊑′C , least)

consistency→lub′ :
  ∀ {A B} → A ~ B → Σ Ty (Lub′ A B)
consistency→lub′ A~B
  with consistency→lub A~B
... | C , (A⊑C , (B⊑C , least)) =
  C , mkLub′
    (⊑→⊑′ A⊑C)
    (⊑→⊑′ B⊑C)
    (λ A⊑′D B⊑′D → ⊑→⊑′ (least (⊑′→⊑ A⊑′D) (⊑′→⊑ B⊑′D)))

lub′→consistency : ∀ {A B} → Σ Ty (Lub′ A B) → A ~ B
lub′→consistency (_ , (A⊑′C , (B⊑′C , least))) =
  upper-bounds-consistent′ A⊑′C B⊑′C

consistency-iff-lub′ :
  ∀ {A B} →
  (A ~ B → Σ Ty (Lub′ A B)) ×
  (Σ Ty (Lub′ A B) → A ~ B)
consistency-iff-lub′ =
  (λ A~B → consistency→lub′ A~B) , lub′→consistency

app-consistency′ :
  ∀ {A B A′ B′} →
  A′ ⊑′ A →
  A ~ B →
  B′ ⊑′ B →
  A′ ~ B′
app-consistency′ A′⊑′A A~B B′⊑′B
  with consistency→lub′ A~B
... | C , (A⊑′C , (B⊑′C , least)) =
  upper-bounds-consistent′
    (⊑′-trans A′⊑′A A⊑′C)
    (⊑′-trans B′⊑′B B⊑′C)

prec-left′ :
  ∀ {X A B} →
  X ⊑′ A →
  A ~ B →
  X ~ B
prec-left′ X⊑′A A~B = app-consistency′ X⊑′A A~B ⊑′-refl

prec-right′ :
  ∀ {A B Y} →
  A ~ B →
  Y ⊑′ B →
  A ~ Y
prec-right′ A~B Y⊑′B = app-consistency′ ⊑′-refl A~B Y⊑′B

ground-consistency-unique :
  ∀ {G H} →
  Ground G →
  Ground H →
  G ~ H →
  G ≡ H
ground-consistency-unique G-ℕ G-ℕ ~-ℕ = refl
ground-consistency-unique G-Bool G-Bool ~-Bool = refl
ground-consistency-unique G-Str G-Str ~-Str = refl
ground-consistency-unique G-⇒★ G-⇒★ (~-⇒ ~-★ ~-★) = refl
ground-consistency-unique G-∀★ G-∀★ (~-∀ ~-★) = refl
ground-consistency-unique G-var G-var ~-X = refl
ground-consistency-unique G-U G-U ~-U = refl
ground-consistency-unique G-ℕ G-Bool ()
ground-consistency-unique G-ℕ G-Str ()
ground-consistency-unique G-ℕ G-⇒★ ()
ground-consistency-unique G-ℕ G-∀★ ()
ground-consistency-unique G-ℕ G-var ()
ground-consistency-unique G-ℕ G-U ()
ground-consistency-unique G-Bool G-ℕ ()
ground-consistency-unique G-Bool G-Str ()
ground-consistency-unique G-Bool G-⇒★ ()
ground-consistency-unique G-Bool G-∀★ ()
ground-consistency-unique G-Bool G-var ()
ground-consistency-unique G-Bool G-U ()
ground-consistency-unique G-Str G-ℕ ()
ground-consistency-unique G-Str G-Bool ()
ground-consistency-unique G-Str G-⇒★ ()
ground-consistency-unique G-Str G-∀★ ()
ground-consistency-unique G-Str G-var ()
ground-consistency-unique G-Str G-U ()
ground-consistency-unique G-⇒★ G-ℕ ()
ground-consistency-unique G-⇒★ G-Bool ()
ground-consistency-unique G-⇒★ G-Str ()
ground-consistency-unique G-⇒★ G-∀★ ()
ground-consistency-unique G-⇒★ G-var ()
ground-consistency-unique G-⇒★ G-U ()
ground-consistency-unique G-∀★ G-ℕ ()
ground-consistency-unique G-∀★ G-Bool ()
ground-consistency-unique G-∀★ G-Str ()
ground-consistency-unique G-∀★ G-⇒★ ()
ground-consistency-unique G-∀★ G-var ()
ground-consistency-unique G-∀★ G-U ()
ground-consistency-unique G-var G-ℕ ()
ground-consistency-unique G-var G-Bool ()
ground-consistency-unique G-var G-Str ()
ground-consistency-unique G-var G-⇒★ ()
ground-consistency-unique G-var G-∀★ ()
ground-consistency-unique G-var G-U ()
ground-consistency-unique G-U G-ℕ ()
ground-consistency-unique G-U G-Bool ()
ground-consistency-unique G-U G-Str ()
ground-consistency-unique G-U G-⇒★ ()
ground-consistency-unique G-U G-∀★ ()
ground-consistency-unique G-U G-var ()

ground-upper-unique :
  ∀ {G H A} →
  Ground G →
  Ground H →
  G ⊑ A →
  H ⊑ A →
  G ≡ H
ground-upper-unique gG gH G⊑A H⊑A =
  ground-consistency-unique gG gH (upper-bounds-consistent G⊑A H⊑A)
