module CastTerms where

-- File Charter:
--   * Intrinsically type-scoped terms for the cast calculus.
--   * Values, typing, and type- and term-variable structural operations.

open import Data.List using (_∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import TyStore
open import TermCtx
open import Primitives
open import Consistency
open import Conversion

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

infix  5 ƛ_
infixl 7 _·_
infix  5 Λ_
infixl 7 _⦂∀_[_]
infixl 7 _⟨_⟩
infixl 7 _↑_ _↓_
infixl 6 _⊕[_]_
infix  9 `_

Var : Set
Var = ℕ

private
  variable
    Δ Δ′ : TyCtx
    A B C D : Ty Δ

data Term : (Δ : TyCtx) → Set where
  `_      : Var → Term Δ
  ƛ_      : Term Δ → Term Δ
  _·_     : Term Δ → Term Δ → Term Δ
  Λ_      : Term (suc Δ) → Term Δ
  _⦂∀_[_] : Term Δ → Ty (suc Δ) → Ty Δ → Term Δ
  $       : Const → Term Δ
  _⊕[_]_  : Term Δ → Prim → Term Δ → Term Δ
  _⟨_⟩    : Term Δ → {μ : Env∼ Δ} {A B : Ty Δ}
    → (c : μ ⊢ A ∼ B) → Term Δ
  _↑_     : Term Δ → {A B : Ty Δ} → Conv↑ Δ A B → Term Δ
  _↓_     : Term Δ → {A B : Ty Δ} → Conv↓ Δ A B → Term Δ
  blame   : Term Δ

private
  variable
    L L′ M M′ N N′ V V′ : Term Δ

------------------------------------------------------------------------
-- Values
------------------------------------------------------------------------

data GenSafe : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  safe-⇒ : ∀ {Δ μ} {A A′ B B′ : Ty Δ}
      {c : μ ⊢ A ∼ A′} {d : μ ⊢ B ∼ B′}
    → GenSafe (c ↦ d)

  safe-∀ : ∀ {Δ μ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
    → GenSafe (∀ᶜ c)

  safe-inst : ∀ {Δ μ} {A : Ty (suc Δ)} {B : Ty Δ}
      {c : instᵐ μ ⊢ A ∼ ⇑ᵗ B}
      ⦃ Anv : NonVar A ⦄ ⦃ z∈A : zero ∈ᵗ A ⦄
    → (B≢★ : B ≢ ★)
    → GenSafe ((inst c) B≢★)

  safe-gen : ∀ {Δ μ} {A : Ty Δ} {B : Ty (suc Δ)}
      {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → GenSafe ((gen c) A≢★)

data Inert : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    → μ ⊢ A ∼ B → Set where
  inj : ∀ {Δ} {μ : Env∼ Δ} {G : Ty Δ}
      ⦃ g : Groundʳ μ X∼★ G ⦄
      ⦃ Gns : NonStar G ⦄ ⦃ match : GroundMatch g G ⦄
    → Inert {μ = μ} ((idᵍ {μ = μ} g) !)

  fun : ∀ {Δ} {μ : Env∼ Δ} {A A′ B B′ : Ty Δ}
      {c : μ ⊢ A ∼ A′} {d : μ ⊢ B ∼ B′}
    → Inert (c ↦ d)

  all : ∀ {Δ} {μ : Env∼ Δ} {A B : Ty (suc Δ)}
      {c : extᵐ μ ⊢ A ∼ B}
    → Inert (∀ᶜ c)

  genᵥ : ∀ {Δ} {μ : Env∼ Δ} {A : Ty Δ}
      {B : Ty (suc Δ)} {c : genᵐ μ ⊢ ⇑ᵗ A ∼ B}
      ⦃ Bnv : NonVar B ⦄ ⦃ z∈B : zero ∈ᵗ B ⦄
    → (A≢★ : A ≢ ★)
    → GenSafe c
    → Inert ((gen c) A≢★)

data RevealValue : ∀ {Δ A B} → Conv↑ Δ A B → Set where
  fun : ∀ {Δ A A′ B B′}
      {c : Conv↓ Δ A′ A} {d : Conv↑ Δ B B′}
    → RevealValue (c ↦↑ d)

  all : ∀ {Δ A B} {c : Conv↑ (suc Δ) A B}
    → RevealValue (`∀↑ c)

data ConcealValue : ∀ {Δ A B} → Conv↓ Δ A B → Set where
  seal : ∀ {Δ} {X : TyVar Δ} {R : Ty Δ}
    → ConcealValue (Conversion.seal X R)

  fun : ∀ {Δ A A′ B B′}
      {c : Conv↑ Δ A′ A} {d : Conv↓ Δ B B′}
    → ConcealValue (c ↦↓ d)

  all : ∀ {Δ A B} {c : Conv↓ (suc Δ) A B}
    → ConcealValue (`∀↓ c)

data Value {Δ : TyCtx} : Term Δ → Set where
  ƛ_ : (N : Term Δ) → Value (ƛ N)
  Λ_ : {V : Term (suc Δ)} → Value V → Value (Λ V)
  $ : (k : Const) → Value ($ k)
  _《_》 : {V : Term Δ}{μ : Env∼ Δ}{A B : Ty Δ}
      {c : μ ⊢ A ∼ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)
  _↑_ : {V : Term Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
    → Value V → RevealValue c → Value (V ↑ c)
  _↓_ : {V : Term Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
    → Value V → ConcealValue c → Value (V ↓ c)

--------------------------------------------------------------------------------
-- Typing
--------------------------------------------------------------------------------

record Ctx : Set where
  constructor ⟨_,_,_⟩
  field
    Δᵉ : TyCtx
    Σᵉ : TyStore Δᵉ
    Γᵉ : TermCtx Δᵉ

open Ctx public

infixl 5 _,ᶜ_
infixl 5 _,ˢ_
infix 4 _∋ᵗ_⦂_
infix 4 _∋ˢ_⦂_

_,ᶜ_ : (Γ : Ctx) → Ty (Δᵉ Γ) → Ctx
⟨ Δ , Σ , Γ ⟩ ,ᶜ A = ⟨ Δ , Σ , A ∷ Γ ⟩

_,ˢ_ : (Γ : Ctx) → Ty (Δᵉ Γ) → Ctx
⟨ Δ , Σ , Γ ⟩ ,ˢ A =
  ⟨ suc Δ , store-bind Σ A , ⇑ᶜ Γ ⟩

⇑ᵉᵗ : Ctx → Ctx
⇑ᵉᵗ ⟨ Δ , Σ , Γ ⟩ = ⟨ suc Δ , store-lift Σ , ⇑ᶜ Γ ⟩

_∋ᵗ_⦂_ : (Γ : Ctx) → Var → Ty (Δᵉ Γ) → Set
⟨ Δ , Σ , Γ ⟩ ∋ᵗ x ⦂ A = TermCtx._∋_⦂_ Γ x A

_∋ˢ_⦂_ : (Γ : Ctx) → TyVar (Δᵉ Γ) → Ty (Δᵉ Γ) → Set
⟨ Δ , Σ , Γ ⟩ ∋ˢ X ⦂ A = TyStore._∋_⦂_ Σ X A

infix 4 _⊢_⦂_

data _⊢_⦂_ (Γ : Ctx) : Term (Δᵉ Γ) → Ty (Δᵉ Γ) → Set where

  ⊢` : ∀ {x A}
     → Γ ∋ᵗ x ⦂ A
      ----------------
     → Γ ⊢ (` x) ⦂ A

  ⊢ƛ : ∀ {A B M}
     → Γ ,ᶜ A ⊢ M ⦂ B
      --------------------
     → Γ ⊢ (ƛ M) ⦂ (A ⇒ B)

  ⊢· : ∀ {A B L M}
     → Γ ⊢ L ⦂ (A ⇒ B)
     → Γ ⊢ M ⦂ A
      -----------------
     → Γ ⊢ (L · M) ⦂ B

  ⊢Λ : ∀ {A M}
     → Value M
     → ⇑ᵉᵗ Γ ⊢ M ⦂ A
      --------------------
     → Γ ⊢ (Λ M) ⦂ (`∀ A)

  ⊢• : ∀ {C A L}
     → Γ ⊢ L ⦂ `∀ C
      ----------------------
     → Γ ⊢ L ⦂∀ C [ A ] ⦂ C [ A ]ᵗ

  ⊢$ : ∀ (κ : Const)
      -----------------------
     → Γ ⊢ ($ κ) ⦂ constTy κ

  ⊢⊕ : ∀ {L M}
     → (op : Prim)
     → Γ ⊢ L ⦂ primArgTy op
     → Γ ⊢ M ⦂ primArgTy op
      -------------------------------------
     → Γ ⊢ (L ⊕[ op ] M) ⦂ primResultTy op

  ⊢⟨⟩ : ∀ {M A B μ}
      → Γ ⊢ M ⦂ A
      → (c : μ ⊢ A ∼ B)
      ---------------------
      → Γ ⊢ M ⟨ c ⟩ ⦂ B

  ⊢reveal : ∀ {M A B} {c : Conv↑ (Δᵉ Γ) A B}
      → Σᵉ Γ ⊢↑ c
      → Γ ⊢ M ⦂ A
      ---------------------
      → Γ ⊢ M ↑ c ⦂ B

  ⊢conceal : ∀ {M A B} {c : Conv↓ (Δᵉ Γ) A B}
      → Σᵉ Γ ⊢↓ c
      → Γ ⊢ M ⦂ A
      ---------------------
      → Γ ⊢ M ↓ c ⦂ B

  ⊢blame : ∀ {A}
      ---------------
    → Γ ⊢ blame ⦂ A

------------------------------------------------------------------------
-- Type-variable renaming
------------------------------------------------------------------------

renameᵗᵐ : Δ ↪ᵗ Δ′ → Term Δ → Term Δ′
renameᵗᵐ ρ (` x) = ` x
renameᵗᵐ ρ (ƛ M) = ƛ renameᵗᵐ ρ M
renameᵗᵐ ρ (L · M) = renameᵗᵐ ρ L · renameᵗᵐ ρ M
renameᵗᵐ ρ (Λ M) = Λ (renameᵗᵐ (keep ρ) M)
renameᵗᵐ ρ (L ⦂∀ C [ A ]) =
  renameᵗᵐ ρ L ⦂∀ renameᵗ (toRenameᵗ (keep ρ)) C
    [ renameᵗ (toRenameᵗ ρ) A ]
renameᵗᵐ ρ ($ κ) = $ κ
renameᵗᵐ ρ (L ⊕[ op ] M) =
  renameᵗᵐ ρ L ⊕[ op ] renameᵗᵐ ρ M
renameᵗᵐ ρ (M ⟨ c ⟩) = renameᵗᵐ ρ M ⟨ renameᵐᶜ ρ c ⟩
renameᵗᵐ ρ (M ↑ c) =
  renameᵗᵐ ρ M ↑ rename↑ (toRenameᵗ ρ) c
renameᵗᵐ ρ (M ↓ c) =
  renameᵗᵐ ρ M ↓ rename↓ (toRenameᵗ ρ) c
renameᵗᵐ ρ blame = blame

⇑ᵗᵐ : Term Δ → Term (suc Δ)
⇑ᵗᵐ = renameᵗᵐ wk↪ᵗ

------------------------------------------------------------------------
-- Term-variable renaming
------------------------------------------------------------------------

Rename : Set
Rename = Var → Var

ext : Rename → Rename
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

rename : Rename → Term Δ → Term Δ
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ M) = ƛ rename (ext ρ) M
rename ρ (L · M) = rename ρ L · rename ρ M
rename ρ (Λ M) = Λ (rename ρ M)
rename ρ (L ⦂∀ C [ A ]) = rename ρ L ⦂∀ C [ A ]
rename ρ ($ κ) = $ κ
rename ρ (L ⊕[ op ] M) = rename ρ L ⊕[ op ] rename ρ M
rename ρ (M ⟨ c ⟩) = rename ρ M ⟨ c ⟩
rename ρ (M ↑ c) = rename ρ M ↑ c
rename ρ (M ↓ c) = rename ρ M ↓ c
rename ρ blame = blame

------------------------------------------------------------------------
-- Term-variable substitution
------------------------------------------------------------------------

Subst : TyCtx → Set
Subst Δ = Var → Term Δ

exts : Subst Δ → Subst Δ
exts σ zero = ` zero
exts σ (suc x) = rename suc (σ x)

liftˢ : Subst Δ → Subst (suc Δ)
liftˢ σ x = ⇑ᵗᵐ (σ x)

subst : Subst Δ → Term Δ → Term Δ
subst σ (` x) = σ x
subst σ (ƛ M) = ƛ subst (exts σ) M
subst σ (L · M) = subst σ L · subst σ M
subst σ (Λ M) = Λ (subst (liftˢ σ) M)
subst σ (L ⦂∀ C [ A ]) = subst σ L ⦂∀ C [ A ]
subst σ ($ κ) = $ κ
subst σ (L ⊕[ op ] M) = subst σ L ⊕[ op ] subst σ M
subst σ (M ⟨ c ⟩) = subst σ M ⟨ c ⟩
subst σ (M ↑ c) = subst σ M ↑ c
subst σ (M ↓ c) = subst σ M ↓ c
subst σ blame = blame

singleSub : Term Δ → Subst Δ
singleSub N zero = N
singleSub N (suc x) = ` x

infixl 8 _[_]
_[_] : Term Δ → Term Δ → Term Δ
M [ N ] = subst (singleSub N) M
