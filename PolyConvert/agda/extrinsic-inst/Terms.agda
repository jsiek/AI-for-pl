module Terms where

-- File Charter:
--   * Extrinsic term syntax and typing judgment for PolyConvert.
--   * `⇑`/`⇓` carry raw type-imprecision evidence.
--   * `↑`/`↓` carry raw conversion evidence.
--   * Term-variable renaming and substitution live here for reduction rules.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _+_; zero; suc)

open import Types
open import Ctx using (⤊ᵗ)
open import Imprecision
  using
    ( Imp
    ; _∣_⊢_⦂_⊑_
    ; _∣_⊢_⦂_⊒_
    ; plains
    ; X⊑★
    ; A⊑★
    ; A⇒B⊑A′⇒B′
    ; `∀A⊑∀B
    ; `∀A⊑B
    ; substImp
    )
open import Conversion

------------------------------------------------------------------------
-- Constants and primitive operators
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

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_⇒_
infix  5 Λ_
infixl 7 _·_
infixl 7 _⦂∀_[_]
infixl 7 _⇑_
infixl 7 _⇓_
infixl 7 _↑_
infixl 7 _↓_
infixl 6 _⊕[_]_
infix  9 `_

data Term : Set where
  `_      : Var → Term
  ƛ_⇒_    : Ty → Term → Term
  _·_     : Term → Term → Term
  Λ_      : Term → Term
  _⦂∀_[_] : Term → Ty → Ty → Term
  $       : Const → Term
  _⊕[_]_  : Term → Prim → Term → Term
  _⇑_     : Term → Imp → Term
  _⇓_     : Term → Imp → Term
  _↑_     : Term → Conv↑ → Term
  _↓_     : Term → Conv↓ → Term
  blame   : Label → Term

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data UpValue : Imp → Set where
  tagν : ∀ {X} →
    UpValue (X⊑★ X)

  tag : ∀ {p} →
    UpValue (A⊑★ p)

  _↦_ : ∀ {p q} →
    UpValue (A⇒B⊑A′⇒B′ p q)

  `∀ : ∀ {p} →
    UpValue (`∀A⊑∀B p)

data DownValue : Imp → Set where
  _↦_ : ∀ {p q} →
    DownValue (A⇒B⊑A′⇒B′ p q)

  `∀ : ∀ {p} →
    DownValue (`∀A⊑∀B p)

  ν_ : ∀ {B p} →
    DownValue (`∀A⊑B B p)

data RevealValue : Conv↑ → Set where
  _↦_ : ∀ {p q} →
    RevealValue (↑-⇒ p q)

  `∀ : ∀ {c} →
    RevealValue (↑-∀ c)

data ConcealValue : Conv↓ → Set where
  seal : ∀ {α} →
    ConcealValue (↓-seal α)

  _↦_ : ∀ {p q} →
    ConcealValue (↓-⇒ p q)

  `∀ : ∀ {c} →
    ConcealValue (↓-∀ c)

data Value : Term → Set where
  ƛ_⇒_ :
    (A : Ty) (N : Term) →
    Value (ƛ A ⇒ N)

  $ :
    (κ : Const) →
    Value ($ κ)

  Λ_ :
    (N : Term) →
    Value (Λ N)

  _⇑_ : ∀ {V : Term} {p : Imp} →
    Value V →
    UpValue p →
    Value (V ⇑ p)

  _⇓_ : ∀ {V : Term} {p : Imp} →
    Value V →
    DownValue p →
    Value (V ⇓ p)

  _↑_ : ∀ {V : Term} {c : Conv↑} →
    Value V →
    RevealValue c →
    Value (V ↑ c)

  _↓_ : ∀ {V : Term} {c : Conv↓} →
    Value V →
    ConcealValue c →
    Value (V ↓ c)

------------------------------------------------------------------------
-- Typing
------------------------------------------------------------------------

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
     → Value M
     → (suc Δ) ∣ Ψ ∣ ⟰ᵗ Σ ∣ (⤊ᵗ Γ) ⊢ M ⦂ A
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {M B T}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (`∀ B)
     → WfTy (suc Δ) Ψ B
     → WfTy Δ Ψ T
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M ⦂∀ B [ T ]) ⦂ B [ T ]ᵗ

  ⊢$ : ∀ (κ : Const)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ L ⦂ (‵ `ℕ)
     → (op : Prim)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ (‵ `ℕ)
     → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (L ⊕[ op ] M) ⦂ (‵ `ℕ)

  ⊢up : ∀ {M A B p}
      → Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊑ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M ⇑ p) ⦂ B

  ⊢down : ∀ {M A B p}
      → Ψ ∣ plains Δ [] ⊢ p ⦂ A ⊒ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (M ⇓ p) ⦂ B

  ⊢reveal : ∀ {M A B c}
      → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↑ˢ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ↑ c ⦂ B

  ⊢conceal : ∀ {M A B c}
      → Δ ∣ Ψ ∣ Σ ⊢ c ⦂ A ↓ˢ B
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ⦂ A
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ M ↓ c ⦂ B

  ⊢blame : ∀ {A}
      → (ℓ : Label)
      → Δ ∣ Ψ ∣ Σ ∣ Γ ⊢ (blame ℓ) ⦂ A

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Renameˣ : Set
Renameˣ = Var → Var

Substˣ : Set
Substˣ = Var → Term

extʳ : Renameˣ → Renameˣ
extʳ ρ zero = zero
extʳ ρ (suc x) = suc (ρ x)

renameˣᵐ : Renameˣ → Term → Term
renameˣᵐ ρ (` x) = ` (ρ x)
renameˣᵐ ρ (ƛ A ⇒ M) = ƛ A ⇒ renameˣᵐ (extʳ ρ) M
renameˣᵐ ρ (L · M) = renameˣᵐ ρ L · renameˣᵐ ρ M
renameˣᵐ ρ (Λ M) = Λ (renameˣᵐ ρ M)
renameˣᵐ ρ (M ⦂∀ B [ T ]) = renameˣᵐ ρ M ⦂∀ B [ T ]
renameˣᵐ ρ ($ κ) = $ κ
renameˣᵐ ρ (L ⊕[ op ] M) = renameˣᵐ ρ L ⊕[ op ] renameˣᵐ ρ M
renameˣᵐ ρ (M ⇑ p) = renameˣᵐ ρ M ⇑ p
renameˣᵐ ρ (M ⇓ p) = renameˣᵐ ρ M ⇓ p
renameˣᵐ ρ (M ↑ c) = renameˣᵐ ρ M ↑ c
renameˣᵐ ρ (M ↓ c) = renameˣᵐ ρ M ↓ c
renameˣᵐ ρ (blame ℓ) = blame ℓ

extˢˣ : Substˣ → Substˣ
extˢˣ σ zero = ` zero
extˢˣ σ (suc x) = renameˣᵐ suc (σ x)

substˣᵐ : Substˣ → Term → Term
substˣᵐ σ (` x) = σ x
substˣᵐ σ (ƛ A ⇒ M) = ƛ A ⇒ substˣᵐ (extˢˣ σ) M
substˣᵐ σ (L · M) = substˣᵐ σ L · substˣᵐ σ M
substˣᵐ σ (Λ M) = Λ (substˣᵐ σ M)
substˣᵐ σ (M ⦂∀ B [ T ]) = substˣᵐ σ M ⦂∀ B [ T ]
substˣᵐ σ ($ κ) = $ κ
substˣᵐ σ (L ⊕[ op ] M) = substˣᵐ σ L ⊕[ op ] substˣᵐ σ M
substˣᵐ σ (M ⇑ p) = substˣᵐ σ M ⇑ p
substˣᵐ σ (M ⇓ p) = substˣᵐ σ M ⇓ p
substˣᵐ σ (M ↑ c) = substˣᵐ σ M ↑ c
substˣᵐ σ (M ↓ c) = substˣᵐ σ M ↓ c
substˣᵐ σ (blame ℓ) = blame ℓ

singleEnv : Term → Substˣ
singleEnv N zero = N
singleEnv N (suc x) = ` x

infixl 8 _[_]
_[_] : Term → Term → Term
M [ N ] = substˣᵐ (singleEnv N) M

substᵗᵐ : Substᵗ → Term → Term
substᵗᵐ σ (` x) = ` x
substᵗᵐ σ (ƛ A ⇒ M) = ƛ substᵗ σ A ⇒ substᵗᵐ σ M
substᵗᵐ σ (L · M) = substᵗᵐ σ L · substᵗᵐ σ M
substᵗᵐ σ (Λ M) = Λ (substᵗᵐ (extsᵗ σ) M)
substᵗᵐ σ (M ⦂∀ B [ T ]) =
  substᵗᵐ σ M ⦂∀ substᵗ (extsᵗ σ) B [ substᵗ σ T ]
substᵗᵐ σ ($ κ) = $ κ
substᵗᵐ σ (L ⊕[ op ] M) = substᵗᵐ σ L ⊕[ op ] substᵗᵐ σ M
substᵗᵐ σ (M ⇑ p) = substᵗᵐ σ M ⇑ substImp σ p
substᵗᵐ σ (M ⇓ p) = substᵗᵐ σ M ⇓ substImp σ p
substᵗᵐ σ (M ↑ c) = substᵗᵐ σ M ↑ substConv↑ᵗ σ c
substᵗᵐ σ (M ↓ c) = substᵗᵐ σ M ↓ substConv↓ᵗ σ c
substᵗᵐ σ (blame ℓ) = blame ℓ

infixl 8 _[_]ᵀ
_[_]ᵀ : Term → Ty → Term
M [ T ]ᵀ = substᵗᵐ (singleTyEnv T) M

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
