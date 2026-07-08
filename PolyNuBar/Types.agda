module Types where

-- File Charter:
--   * Core PolyNuBar type syntax, contexts, type well-formedness, and
--     type-level renaming/substitution.
--   * Uses natural-number de Bruijn indices for type variables.
--   * Keeps the operational semantics and term-level substitution in their
--     own modules.

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<_; _≟_; zero; suc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

------------------------------------------------------------------------
-- Variables, types, contexts
------------------------------------------------------------------------

Var : Set
Var = ℕ

SealVar : Set
SealVar = ℕ

data Base : Set where
  𝕀 : Base
  𝔹 : Base

infixr 7 _⇒_
infixr 6 _`×_
infix  5 `∀_
infix  9 `_

data Ty : Set where
  `_   : Var → Ty
  `ι   : Base → Ty
  ★    : Ty
  _⇒_  : Ty → Ty → Ty
  _`×_ : Ty → Ty → Ty
  `∀_  : Ty → Ty

infixl 4 _▷ᵗ
infixl 4 _▷ᵇ_
infixl 4 _▷ˢ_
infixl 4 _▷ᵛ_

data Ctx : Set where
  ∅    : Ctx
  _▷ᵗ  : Ctx → Ctx
  _▷ᵇ_ : Ctx → SealVar → Ctx
  _▷ˢ_ : Ctx → Ty → Ctx
  _▷ᵛ_ : Ctx → Ty → Ctx

------------------------------------------------------------------------
-- Type-variable renaming and substitution
------------------------------------------------------------------------

Renameᵗ : Set
Renameᵗ = Var → Var

Substᵗ : Set
Substᵗ = Var → Ty

renᵗ : Renameᵗ → Substᵗ
renᵗ ρ X = ` (ρ X)

extᵗ : Renameᵗ → Renameᵗ
extᵗ ρ zero = zero
extᵗ ρ (suc X) = suc (ρ X)

swap₀₁ : Renameᵗ
swap₀₁ zero = suc zero
swap₀₁ (suc zero) = zero
swap₀₁ (suc (suc X)) = suc (suc X)

renameᵗ : Renameᵗ → Ty → Ty
renameᵗ ρ (` X) = ` (ρ X)
renameᵗ ρ (`ι ι) = `ι ι
renameᵗ ρ ★ = ★
renameᵗ ρ (A ⇒ B) = renameᵗ ρ A ⇒ renameᵗ ρ B
renameᵗ ρ (A `× B) = renameᵗ ρ A `× renameᵗ ρ B
renameᵗ ρ (`∀ A) = `∀ renameᵗ (extᵗ ρ) A

⇑ᵗ : Ty → Ty
⇑ᵗ = renameᵗ suc

extsᵗ : Substᵗ → Substᵗ
extsᵗ σ zero = ` zero
extsᵗ σ (suc X) = ⇑ᵗ (σ X)

substᵗ : Substᵗ → Ty → Ty
substᵗ σ (` X) = σ X
substᵗ σ (`ι ι) = `ι ι
substᵗ σ ★ = ★
substᵗ σ (A ⇒ B) = substᵗ σ A ⇒ substᵗ σ B
substᵗ σ (A `× B) = substᵗ σ A `× substᵗ σ B
substᵗ σ (`∀ A) = `∀ substᵗ (extsᵗ σ) A

idᵗ : Substᵗ
idᵗ = `_

infixr 6 _•ᵗ_
_•ᵗ_ : Ty → Substᵗ → Substᵗ
(A •ᵗ σ) zero = A
(A •ᵗ σ) (suc X) = σ X

singleTyEnv : Ty → Substᵗ
singleTyEnv A zero = A
singleTyEnv A (suc X) = ` X

infixl 8 _[_]ᵗ
_[_]ᵗ : Ty → Ty → Ty
A [ B ]ᵗ = substᵗ (singleTyEnv B) A

closeVarAt : ℕ → Ty → Var → Ty
closeVarAt zero C zero = C
closeVarAt zero C (suc X) = ` X
closeVarAt (suc k) C zero = ` zero
closeVarAt (suc k) C (suc X) = renameᵗ suc (closeVarAt k C X)

closeTyAt : ℕ → Ty → Ty → Ty
closeTyAt k C (` X) = closeVarAt k C X
closeTyAt k C (`ι ι) = `ι ι
closeTyAt k C ★ = ★
closeTyAt k C (A ⇒ B) = closeTyAt k C A ⇒ closeTyAt k C B
closeTyAt k C (A `× B) = closeTyAt k C A `× closeTyAt k C B
closeTyAt k C (`∀ A) = `∀ closeTyAt (suc k) C A

substAt : Var → Ty → Ty → Ty
substAt X A B = substᵗ σ B
  where
  σ : Substᵗ
  σ Y with Y ≟ X
  ... | yes refl = A
  ... | no _ = ` Y

infixl 8 _[_/_]ᵗ
_[_/_]ᵗ : Ty → Ty → Var → Ty
B [ A / X ]ᵗ = substAt X A B

------------------------------------------------------------------------
-- Ground types, consistency, store bindings
------------------------------------------------------------------------

data Ground : Ty → Set where
  g-base : ∀ {ι} → Ground (`ι ι)
  g-fun  : Ground (★ ⇒ ★)
  g-prod : Ground (★ `× ★)
  g-var  : ∀ {X} → Ground (` X)

data GroundOf : Ty → Ty → Set where
  go-base : ∀ {ι} → GroundOf (`ι ι) (`ι ι)
  go-fun  : ∀ {A B} → GroundOf (A ⇒ B) (★ ⇒ ★)
  go-prod : ∀ {A B} → GroundOf (A `× B) (★ `× ★)
  go-var  : ∀ {X} → GroundOf (` X) (` X)

infix 4 _∼_
data _∼_ : Ty → Ty → Set where
  ∼-base : ∀ {ι} → (`ι ι) ∼ (`ι ι)
  ∼-★ˡ   : ∀ {A} → ★ ∼ A
  ∼-★ʳ   : ∀ {A} → A ∼ ★
  ∼-var  : ∀ {X} → (` X) ∼ (` X)
  ∼-fun  : ∀ {A A′ B B′} → A ∼ A′ → B ∼ B′ → (A ⇒ B) ∼ (A′ ⇒ B′)
  ∼-prod : ∀ {A A′ B B′} → A ∼ A′ → B ∼ B′ → (A `× B) ∼ (A′ `× B′)
  ∼-∀ˡ   : ∀ {A B} → (A [ ★ ]ᵗ) ∼ B → (`∀ A) ∼ B
  ∼-∀ʳ   : ∀ {A B} → A ∼ (B [ ★ ]ᵗ) → A ∼ (`∀ B)

------------------------------------------------------------------------
-- Telescoped context lookup and well-formed types
------------------------------------------------------------------------

infix 4 _∋ᵗ_
data _∋ᵗ_ : Ctx → Var → Set where
  TZ : ∀ {Γ} → (Γ ▷ᵗ) ∋ᵗ zero
  TZᵇ : ∀ {Γ X} → (Γ ▷ᵇ X) ∋ᵗ zero
  TSᵗ : ∀ {Γ X} → Γ ∋ᵗ X → (Γ ▷ᵗ) ∋ᵗ suc X
  TSᵇ : ∀ {Γ X Y} → Γ ∋ᵗ X → (Γ ▷ᵇ Y) ∋ᵗ suc X
  TSˢ : ∀ {Γ X A} → Γ ∋ᵗ X → (Γ ▷ˢ A) ∋ᵗ X
  TSᵛ : ∀ {Γ X A} → Γ ∋ᵗ X → (Γ ▷ᵛ A) ∋ᵗ X

infix 4 _∋ˢ_:=_
data _∋ˢ_:=_ : Ctx → Var → Ty → Set where
  here  : ∀ {Γ A} → (Γ ▷ˢ A) ∋ˢ zero := A
  thereˢ : ∀ {Γ X A B} → Γ ∋ˢ X := A → (Γ ▷ˢ B) ∋ˢ suc X := A
  thereᵗ : ∀ {Γ X A} → Γ ∋ˢ X := A → (Γ ▷ᵗ) ∋ˢ X := ⇑ᵗ A
  thereᵇ : ∀ {Γ X Y A} → Γ ∋ˢ X := A → (Γ ▷ᵇ Y) ∋ˢ X := ⇑ᵗ A
  thereᵛ : ∀ {Γ X A B} → Γ ∋ˢ X := A → (Γ ▷ᵛ B) ∋ˢ X := A

infix 4 _∋ˢ⁰_:=_
data _∋ˢ⁰_:=_ : Ctx → Var → Ty → Set where
  here⁰  : ∀ {Γ A} → (Γ ▷ˢ A) ∋ˢ⁰ zero := A
  thereˢ⁰ : ∀ {Γ X A B} → Γ ∋ˢ⁰ X := A → (Γ ▷ˢ B) ∋ˢ⁰ suc X := A
  thereᵛ⁰ : ∀ {Γ X A B} → Γ ∋ˢ⁰ X := A → (Γ ▷ᵛ B) ∋ˢ⁰ X := A

store⁰→store : ∀ {Γ X A} → Γ ∋ˢ⁰ X := A → Γ ∋ˢ X := A
store⁰→store here⁰ = here
store⁰→store (thereˢ⁰ X∈) = thereˢ (store⁰→store X∈)
store⁰→store (thereᵛ⁰ X∈) = thereᵛ (store⁰→store X∈)

data PopCtx : SealVar → Ty → ℕ → Ctx → Ctx → Set where
  pop-here :
    ∀ {Γ X C} →
    Γ ∋ˢ X := C →
    PopCtx X C zero (Γ ▷ᵇ X) Γ
  popᵗ :
    ∀ {Γᵒ Γᶜ X C k} →
    PopCtx X C k Γᵒ Γᶜ →
    PopCtx X C (suc k) (Γᵒ ▷ᵗ) (Γᶜ ▷ᵗ)
  popᵇ :
    ∀ {Γᵒ Γᶜ X Y C k} →
    PopCtx X C k Γᵒ Γᶜ →
    PopCtx X C (suc k) (Γᵒ ▷ᵇ Y) (Γᶜ ▷ᵇ Y)
  popˢ :
    ∀ {Γᵒ Γᶜ X C k A A′} →
    PopCtx X C k Γᵒ Γᶜ →
    A′ ≡ closeTyAt k C A →
    PopCtx (suc X) C k (Γᵒ ▷ˢ A) (Γᶜ ▷ˢ A′)
  popᵛ :
    ∀ {Γᵒ Γᶜ X C k A A′} →
    PopCtx X C k Γᵒ Γᶜ →
    A′ ≡ closeTyAt k C A →
    PopCtx X C k (Γᵒ ▷ᵛ A) (Γᶜ ▷ᵛ A′)

infix 4 _∋_⦂_
data _∋_⦂_ : Ctx → Var → Ty → Set where
  Z  : ∀ {Γ A} → (Γ ▷ᵛ A) ∋ zero ⦂ A
  S  : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (Γ ▷ᵛ B) ∋ suc x ⦂ A
  Sᵗ : ∀ {Γ A x} → Γ ∋ x ⦂ A → (Γ ▷ᵗ) ∋ x ⦂ ⇑ᵗ A
  Sᵇ : ∀ {Γ A X x} → Γ ∋ x ⦂ A → (Γ ▷ᵇ X) ∋ x ⦂ ⇑ᵗ A
  Sˢ : ∀ {Γ A B x} → Γ ∋ x ⦂ A → (Γ ▷ˢ B) ∋ x ⦂ A

data WfTy : Ctx → Ty → Set where
  wf-var  : ∀ {Γ X} → Γ ∋ᵗ X → WfTy Γ (` X)
  wf-base : ∀ {Γ ι} → WfTy Γ (`ι ι)
  wf-★    : ∀ {Γ} → WfTy Γ ★
  wf-fun  : ∀ {Γ A B} → WfTy Γ A → WfTy Γ B → WfTy Γ (A ⇒ B)
  wf-prod : ∀ {Γ A B} → WfTy Γ A → WfTy Γ B → WfTy Γ (A `× B)
  wf-∀    : ∀ {Γ A} → WfTy (Γ ▷ᵗ) A → WfTy Γ (`∀ A)

------------------------------------------------------------------------
-- Labels, barrier binders, constants, primitives
------------------------------------------------------------------------

data Label : Set where
  -    : Label
  ℓ_   : ℕ → Label
  bar  : Label → Label

neg : Label → Label
neg - = -
neg (bar p) = p
neg p = bar p

data Binder : Set where
  bind    : SealVar → Binder
  unbind : SealVar → Binder

negBind : Binder → Binder
negBind (bind X) = unbind X
negBind (unbind X) = bind X

var : Binder → SealVar
var (bind X) = X
var (unbind X) = X

data Const : Set where
  int  : ℕ → Const
  bool : Bool → Const

typeOfConst : Const → Ty
typeOfConst (int n) = `ι 𝕀
typeOfConst (bool b) = `ι 𝔹

data Prim : Set where
  add1 one-minus : Prim
  f not positive? : Prim

typeOfPrim : Prim → Ty
typeOfPrim add1 = `ι 𝕀 ⇒ `ι 𝕀
typeOfPrim one-minus = `ι 𝕀 ⇒ `ι 𝕀
typeOfPrim f = `ι 𝔹 ⇒ `ι 𝕀
typeOfPrim not = `ι 𝔹 ⇒ `ι 𝔹
typeOfPrim positive? = `ι 𝕀 ⇒ `ι 𝔹

delta : Prim → Const → Const
delta add1 (int n) = int (suc n)
delta add1 (bool b) = int zero
delta one-minus (int zero) = int (suc zero)
delta one-minus (int (suc n)) = int zero
delta one-minus (bool b) = int zero
delta f (bool true) = int 42
delta f (bool false) = int zero
delta f (int n) = int zero
delta not (bool true) = bool false
delta not (bool false) = bool true
delta not (int n) = bool false
delta positive? (int zero) = bool false
delta positive? (int (suc n)) = bool true
delta positive? (bool b) = bool false
