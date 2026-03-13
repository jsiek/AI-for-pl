module PolyTypes where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; subst)
open import Data.List using (List; []; _∷_; map)
open import Data.Nat using (ℕ; _<_; zero; suc)
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

data NoX : Ty → Set where
  NoX-ℕ    : NoX `ℕ
  NoX-Bool : NoX `Bool
  NoX-Str  : NoX `Str
  NoX-★    : NoX `★
  NoX-U    : ∀ {U} → NoX (`U U)
  NoX-⇒    : ∀ {A B} → NoX A → NoX B → NoX (A ⇒ B)
  NoX-∀    : ∀ {A} → NoX A → NoX (`∀ A)

NoX-renameᵘ :
  ∀ {d ρ A} →
  NoX A →
  NoX (renameᵘ d ρ A)
NoX-renameᵘ NoX-ℕ = NoX-ℕ
NoX-renameᵘ NoX-Bool = NoX-Bool
NoX-renameᵘ NoX-Str = NoX-Str
NoX-renameᵘ NoX-★ = NoX-★
NoX-renameᵘ NoX-U = NoX-U
NoX-renameᵘ (NoX-⇒ nxA nxB) =
  NoX-⇒ (NoX-renameᵘ nxA) (NoX-renameᵘ nxB)
NoX-renameᵘ (NoX-∀ nxA) = NoX-∀ (NoX-renameᵘ nxA)

NoX-[]ᵘ :
  ∀ {A U} →
  NoX A →
  NoX (A [ U ]ᵘ)
NoX-[]ᵘ = NoX-renameᵘ

NoX-renameᵘ-id :
  ∀ {d ρ A} →
  NoX A →
  renameᵘ d ρ A ≡ A
NoX-renameᵘ-id NoX-ℕ = refl
NoX-renameᵘ-id NoX-Bool = refl
NoX-renameᵘ-id NoX-Str = refl
NoX-renameᵘ-id NoX-★ = refl
NoX-renameᵘ-id NoX-U = refl
NoX-renameᵘ-id (NoX-⇒ nxA nxB) =
  cong₂ _⇒_ (NoX-renameᵘ-id nxA) (NoX-renameᵘ-id nxB)
NoX-renameᵘ-id (NoX-∀ nxA) =
  cong `∀ (NoX-renameᵘ-id nxA)

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

mutual
  ★~-ty : ∀ A → NoX A → `★ ~ A
  ★~-ty (` X) ()
  ★~-ty `ℕ NoX-ℕ = ★~ℕ
  ★~-ty `Bool NoX-Bool = ★~Bool
  ★~-ty `Str NoX-Str = ★~Str
  ★~-ty `★ NoX-★ = ~-★
  ★~-ty (`U U) NoX-U = ★~U
  ★~-ty (A ⇒ B) (NoX-⇒ nxA nxB) = ★~⇒ (~★-ty A nxA) (★~-ty B nxB)
  ★~-ty (`∀ A) (NoX-∀ nxA) =
    ★~∀
      (subst
        (λ T → `★ ~ T)
        (sym (NoX-renameᵘ-id {d = 0} {ρ = singleᵘ 0} nxA))
        (★~-ty A nxA))

  ~★-ty : ∀ A → NoX A → A ~ `★
  ~★-ty (` X) ()
  ~★-ty `ℕ NoX-ℕ = ℕ~★
  ~★-ty `Bool NoX-Bool = Bool~★
  ~★-ty `Str NoX-Str = Str~★
  ~★-ty `★ NoX-★ = ~-★
  ~★-ty (`U U) NoX-U = U~★
  ~★-ty (A ⇒ B) (NoX-⇒ nxA nxB) = ⇒~★ (★~-ty A nxA) (~★-ty B nxB)
  ~★-ty (`∀ A) (NoX-∀ nxA) =
    ∀~★
      (subst
        (λ T → T ~ `★)
        (sym (NoX-renameᵘ-id {d = 0} {ρ = singleᵘ 0} nxA))
        (~★-ty A nxA))

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

⊑-NoX-left : ∀ {A B} → A ⊑ B → NoX B → NoX A
⊑-NoX-left ⊑-X ()
⊑-NoX-left ⊑-ℕ NoX-ℕ = NoX-ℕ
⊑-NoX-left ⊑-Bool NoX-Bool = NoX-Bool
⊑-NoX-left ⊑-Str NoX-Str = NoX-Str
⊑-NoX-left ⊑-U NoX-U = NoX-U
⊑-NoX-left (⊑-★ nxB) nxB' = NoX-★
⊑-NoX-left (⊑-⇒ A⊑C B⊑D) (NoX-⇒ nxC nxD) =
  NoX-⇒ (⊑-NoX-left A⊑C nxC) (⊑-NoX-left B⊑D nxD)
⊑-NoX-left (⊑-∀ A⊑B) (NoX-∀ nxB) =
  NoX-∀ (⊑-NoX-left A⊑B nxB)

⊑-NoX-right : ∀ {A B} → NoX A → A ⊑ B → NoX B
⊑-NoX-right NoX-ℕ ⊑-ℕ = NoX-ℕ
⊑-NoX-right NoX-Bool ⊑-Bool = NoX-Bool
⊑-NoX-right NoX-Str ⊑-Str = NoX-Str
⊑-NoX-right NoX-★ (⊑-★ nxB) = nxB
⊑-NoX-right NoX-U ⊑-U = NoX-U
⊑-NoX-right (NoX-⇒ nxA nxB) (⊑-⇒ A⊑C B⊑D) =
  NoX-⇒ (⊑-NoX-right nxA A⊑C) (⊑-NoX-right nxB B⊑D)
⊑-NoX-right (NoX-∀ nxA) (⊑-∀ A⊑B) = NoX-∀ (⊑-NoX-right nxA A⊑B)

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
    ∀ {A B} → A ~ B → NoX A → NoX B → Σ Ty (Lub A B)
  consistency→lub ~-X () _
  consistency→lub ~-ℕ NoX-ℕ NoX-ℕ =
    `ℕ , mkLub ⊑-ℕ ⊑-ℕ (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-Bool NoX-Bool NoX-Bool =
    `Bool , mkLub ⊑-Bool ⊑-Bool (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-Str NoX-Str NoX-Str =
    `Str , mkLub ⊑-Str ⊑-Str (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-★ NoX-★ NoX-★ =
    `★ , mkLub (⊑-★ NoX-★) (⊑-★ NoX-★) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ~-U NoX-U NoX-U =
    `U _ , mkLub ⊑-U ⊑-U (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~ℕ NoX-★ NoX-ℕ =
    `ℕ , mkLub (⊑-★ NoX-ℕ) ⊑-ℕ (λ A⊑D B⊑D → B⊑D)
  consistency→lub ℕ~★ NoX-ℕ NoX-★ =
    `ℕ , mkLub ⊑-ℕ (⊑-★ NoX-ℕ) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~Bool NoX-★ NoX-Bool =
    `Bool , mkLub (⊑-★ NoX-Bool) ⊑-Bool (λ A⊑D B⊑D → B⊑D)
  consistency→lub Bool~★ NoX-Bool NoX-★ =
    `Bool , mkLub ⊑-Bool (⊑-★ NoX-Bool) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~Str NoX-★ NoX-Str =
    `Str , mkLub (⊑-★ NoX-Str) ⊑-Str (λ A⊑D B⊑D → B⊑D)
  consistency→lub Str~★ NoX-Str NoX-★ =
    `Str , mkLub ⊑-Str (⊑-★ NoX-Str) (λ A⊑D B⊑D → A⊑D)
  consistency→lub ★~U NoX-★ NoX-U =
    `U _ , mkLub (⊑-★ NoX-U) ⊑-U (λ A⊑D B⊑D → B⊑D)
  consistency→lub U~★ NoX-U NoX-★ =
    `U _ , mkLub ⊑-U (⊑-★ NoX-U) (λ A⊑D B⊑D → A⊑D)
  consistency→lub (★~⇒ A~★ ★~B) NoX-★ (NoX-⇒ nxA nxB) =
    (_ ⇒ _) ,
    mkLub (⊑-★ (NoX-⇒ nxA nxB)) (⊑-⇒ ⊑-refl ⊑-refl)
      (λ A⊑D B⊑D → B⊑D)
  consistency→lub (⇒~★ ★~A B~★) (NoX-⇒ nxA nxB) NoX-★ =
    (_ ⇒ _) ,
    mkLub (⊑-⇒ ⊑-refl ⊑-refl) (⊑-★ (NoX-⇒ nxA nxB))
      (λ A⊑D B⊑D → A⊑D)
  consistency→lub {A = A₁ ⇒ B₁} {B = C₁ ⇒ D₁} (~-⇒ C~A B~D) (NoX-⇒ nxA nxB) (NoX-⇒ nxC nxD)
    with consistency→lub C~A nxC nxA
       | consistency→lub B~D nxB nxD
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
  consistency→lub {A = `∀ A₀} {B = `∀ B₀} (~-∀ A~B) (NoX-∀ nxA) (NoX-∀ nxB)
    with consistency→lub A~B nxA nxB
  ... | J , (A⊑J , (B⊑J , leastBody)) =
    `∀ J , mkLub (⊑-∀ A⊑J) (⊑-∀ B⊑J) least
    where
      least : ∀ {X} → `∀ A₀ ⊑ X → `∀ B₀ ⊑ X → `∀ J ⊑ X
      least (⊑-∀ A⊑X) (⊑-∀ B⊑X) =
        ⊑-∀ (leastBody A⊑X B⊑X)
  consistency→lub (★~∀ ★~A) NoX-★ (NoX-∀ nxA) = `∀ _ ,
    mkLub (⊑-★ (NoX-∀ nxA)) (⊑-∀ ⊑-refl) (λ A⊑D B⊑D → B⊑D)
  consistency→lub (∀~★ A~★) (NoX-∀ nxA) NoX-★ = `∀ _ ,
    mkLub (⊑-∀ ⊑-refl) (⊑-★ (NoX-∀ nxA)) (λ A⊑D B⊑D → A⊑D)

lub→consistency : ∀ {A B} → Σ Ty (Lub A B) → A ~ B
lub→consistency (_ , (A⊑C , (B⊑C , least))) =
  upper-bounds-consistent A⊑C B⊑C

consistency-iff-lub :
  ∀ {A B} →
  NoX A →
  NoX B →
  (A ~ B → Σ Ty (Lub A B)) ×
  (Σ Ty (Lub A B) → A ~ B)
consistency-iff-lub nxA nxB =
  (λ A~B → consistency→lub A~B nxA nxB) , lub→consistency

app-consistency :
  ∀ {A B A′ B′} →
  A′ ⊑ A →
  A ~ B →
  B′ ⊑ B →
  NoX A →
  NoX B →
  A′ ~ B′
app-consistency A′⊑A A~B B′⊑B nxA nxB
  with consistency→lub A~B nxA nxB
... | C , (A⊑C , (B⊑C , least)) =
  upper-bounds-consistent (⊑-trans A′⊑A A⊑C) (⊑-trans B′⊑B B⊑C)

prec-left :
  ∀ {X A B} →
  X ⊑ A →
  A ~ B →
  NoX A →
  NoX B →
  X ~ B
prec-left X⊑A A~B nxA nxB = app-consistency X⊑A A~B ⊑-refl nxA nxB

prec-right :
  ∀ {A B Y} →
  A ~ B →
  Y ⊑ B →
  NoX A →
  NoX B →
  A ~ Y
prec-right A~B Y⊑B nxA nxB = app-consistency ⊑-refl A~B Y⊑B nxA nxB

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
